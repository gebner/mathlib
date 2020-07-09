import tactic.hammer.feature_search system.io tactic.core meta.coinductive_predicates
  tactic.hammer.fol super tactic.hammer.fo_translation2

namespace hammer

open tactic expr native

meta def is_good_const : name → Prop
| ``Exists := ff
| _ := tt

meta instance : decidable_pred is_good_const :=
by delta is_good_const; apply_instance

meta def close_under_references_core : list name → rb_set name → tactic (rb_set name)
| [] s := pure s
| (n::ns) s :=
  if s.contains n then
    close_under_references_core ns s
  else do
    cs ← (do d ← get_decl n, pure $ some $ d.type.constants.filter is_good_const) <|> pure none,
    match cs with
    | none := close_under_references_core ns s
    | some cs := close_under_references_core (cs ++ ns) (s.insert n)
    end

meta def close_under_references (ns : list name) : tactic (list name) :=
rb_set.to_list <$> close_under_references_core ns mk_rb_set

meta def close_under_equations (ns : list name) : tactic (list name) :=
(list.dup_by_native id ∘ (++ ns) ∘ list.join) <$>
  ns.mmap (λ n, get_eqn_lemmas_for tt n <|> pure [])

meta def mk_h_defeq (e1 e2 : expr) (t1 t2 : expr) : tactic expr := do
(xs1, t1) ← mk_meta_pis t1,
(xs2, t2) ← mk_meta_pis t2,
unify t1 t2,
let e1 := e1.app_of_list xs1,
let e2 := e2.app_of_list xs2,
unify e1 e2,
e1 ← instantiate_mvars e1,
e2 ← instantiate_mvars e2,
guard $ ¬ e1.has_meta_var ∧ ¬ e2.has_meta_var,
mk_app ``eq [e1, e2]

meta def mk_h_defeq_decl (n1 n2 : name) : tactic expr := do
(e1, t1) ← get_decl n1 >>= decl_mk_const,
(e2, t2) ← get_decl n2 >>= decl_mk_const,
mk_h_defeq e1 e2 t1 t2

-- #eval mk_h_defeq_decl ``nat.semiring ``comm_semiring.to_semiring >>= trace

open fotr2

meta def trans.run {α} (t : trans α) : tactic α :=
prod.fst <$> (show state_t _ tactic α, from t).run {
  cam_cfg := {
    drop_subsingleton := ff,
    drop_inst_args := ff,
    drop_dep_args := ff,
    param_all_args := ff,
    param_all_cls_args := ff,
  },
}

meta def add_instance_defeq (i1 i2 : name) : trans unit :=
(do eqn@`(%%lhs = %%rhs) ← state_t.lift $ mk_h_defeq_decl i1 i2 | failure,
    n ← fresh_name `_instance_defeq,
    prf ← state_t.lift $ mk_eq_refl lhs,
    trans_decl n prf eqn
) <|> pure ()

meta def add_instance_defeqs (axs : list name) : trans unit := do
is ← state_t.lift $ axs.mfilter is_instance,
monad.sequence' $ do
  i1 ← is,
  i2 ← is,
  guard $ i1 < i2,
  [add_instance_defeq i1 i2]

meta def do_trans (axs : list name) (goal : expr) : tactic (format × list (string × name)) := trans.run $ do
let axs := goal.constants.filter is_good_const ++ axs,
axs ← state_t.lift $ close_under_references axs,
axs ← state_t.lift $ close_under_instances axs,
state_t.lift $ trace axs,
axs ← state_t.lift $ close_under_equations axs,
axs ← state_t.lift $ close_under_references axs,
state_t.lift $ trace $ (axs.map name.to_string).qsort (λ a b, a < b),
axs.mmap' (λ n, do d ← state_t.lift $ get_decl n, trans_decl' d),
add_instance_defeqs axs,
goal_is_prop ← state_t.lift $ tactic.is_prop goal,
goal' ← if goal_is_prop then trans_fml [] goal
  else (do x' ← state_t.lift $ mk_local_def `_goal goal,
           x ← get_var_name x',
           fo_fml.ex x <$> trans_type [] x' goal),
out ← trans_state.out <$> get,
let anns := out.map $ λ o, tptpify_ann "axiom" o.n o.fml,
let anns := (tptpify_ann "conjecture" `_goal goal') :: anns,
let (anns, _) := (monad.sequence anns).run mk_name_map,
let tptp := format.join $ list.intersperse (format.line ++ format.line) anns.reverse,
pure (tptp, out.map (λ o, (ax_tptpify_name' o.n, o.n)))

-- #eval do_trans [
--   ``nat.prod_dvd_and_dvd_of_dvd_prod,
-- --  ``heq.drec_on,
--  ``nat.exists_coprime
-- ] `(
--   ∀ {m n : ℕ} (H : 0 < nat.gcd m n),
--   ∃ g m' n', 0 < g ∧ nat.coprime m' n' ∧ m = m' * g ∧ n = n' * g
-- ) >>= tactic.trace

section

meta def exec_cmd (cmd : string) (args : list string) (stdin : string) : tactic string :=
tactic.unsafe_run_io $ do
child ← io.proc.spawn {
  cmd := cmd, args := args,
  stdin := io.process.stdio.piped,
  stdout := io.process.stdio.piped,
},
io.fs.write child.stdin stdin.to_char_buffer,
io.fs.close child.stdin,
buf ← io.fs.read_to_end child.stdout,
io.fs.close child.stdout,
exitv ← io.proc.wait child,
when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
return buf.to_string

meta def run_vampire (tptp : string) : tactic string :=
exec_cmd "vampire" ["-p", "tptp"] tptp

end

meta def filter_lemmas1 (axs : list name) (goal : expr) : tactic (list name) := do
(tptp, ax_names) ← do_trans axs goal,
(tactic.unsafe_run_io $ do f ← io.mk_file_handle "hammer.p" io.mode.write, io.fs.write f tptp.to_string.to_char_buffer, io.fs.close f),
let ax_names := rb_map.of_list ax_names,
tptp_out ← timetac "vampire took" $ exec_cmd "bash" ["-c",
  "vampire -p tptp -t 30s --output_axiom_names on | " ++
    "grep -oP '(?<=file\\(unknown,).*?(?=\\))'"]
  tptp.to_string,
let ns := tptp_out.split_on '\n',
pure $ do n ← ns, (ax_names.find n).to_list

meta def find_lemmas1 (goal : expr) (max := 10) : tactic (list name) := do
env ← get_env,
axs ← timetac "Premise selection took" $ pure $ select_for_goal env goal,
let axs := (axs.take max).map (λ a, a.1),
-- trace "Premise selection:",
trace axs,
timetac "Lemma filtering took" $ filter_lemmas1 axs goal

meta def reconstruct1 (axs : list name) : tactic unit :=
focus1 $ super.with_ground_mvars $ do
axs ← list.join <$> (axs.mmap $ λ ax,
  pure <$> (mk_const ax >>= super.clause.of_proof) <|> pure []),
axs ← (++ axs) <$> (tactic.local_context >>= list.mmap super.clause.of_proof),
super.solve_with_goal {} axs

-- set_option profiler true
-- #eval do
-- let goal : expr := `(∀ x y : nat, x < y ∨ x ≥ y),
-- let goal : expr := `(∀ x : nat, x ≤ x),
-- axs ← select_for_goal' goal,
-- -- let axs := [(``nat.le_succ, ()), (``le_refl, ())],
-- (tptp, _) ← do_trans ((axs.take 20).map prod.fst) goal,
-- trace tptp

end hammer

namespace tactic

namespace interactive

open interactive interactive.types lean.parser

private meta def find_lemmas1_core (axs : option (list name)) (max_lemmas : ℕ) : tactic (list name) := do
goal ← reverted_target,
lems ←
  match axs with
  | none := hammer.find_lemmas1 goal max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "Lemma filtering took" $
      hammer.filter_lemmas1 axs goal
  end,
trace $ to_fmt "\nTry this: super " ++ (to_fmt lems).group,
pure lems

meta def find_lemmas1 (axs : parse $ optional $ list_of ident) (max_lemmas := 10) : tactic unit := do
find_lemmas1_core axs max_lemmas,
admit

meta def hammer1 (axs : parse $ optional $ list_of ident) (max_lemmas := 10) : tactic unit := do
lems ← find_lemmas1_core axs max_lemmas,
tactic.intros,
hammer.reconstruct1 lems

end interactive
end tactic
