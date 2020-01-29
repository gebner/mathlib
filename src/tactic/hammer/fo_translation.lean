import tactic.hammer.feature_search system.io tactic.core meta.coinductive_predicates
tactic.hammer.fol super

def list.zip_extend {α β} (a : α) : list α → list β → list (α × β)
| (a::as) (b::bs) := (a,b) :: list.zip_extend as bs
| [] (b::bs) := (a,b) :: list.zip_extend [] bs
| _ [] := []

namespace hammer

open tactic expr native

structure trans_state :=
(fresh_idx : ℕ)
(out : list (name × fo_fml))

@[reducible]
meta def trans := state_t trans_state tactic

meta def trans.run {α} (t : trans α) : tactic α :=
prod.fst <$> (show state_t _ tactic α, from t).run {
  fresh_idx := 0,
  out := [],
}

meta def trans.get_out : trans (list (name × fo_fml)) :=
do s ← state_t.get, pure s.out

meta def trans.decl_out (n : name) (f : fo_fml) : trans unit :=
state_t.modify $ λ s, { out := (n, f) :: s.out, ..s }

meta def fresh_num : trans ℕ := do
state_t.modify (λ s, { fresh_idx := s.fresh_idx + 1, ..s }),
trans_state.fresh_idx <$> state_t.get

meta def fresh_name (hint : name) : trans name :=
do n ← fresh_num, pure $ name.mk_numeral (unsigned.of_nat n) hint

meta def trans_var (n : name) (t : expr) (bi : binder_info := binder_info.default) :
  trans (name × expr) := do
x' ← fresh_name n,
pure (x', local_const x' x' bi t)

private meta def contained_lconsts' : expr → rb_map name expr → rb_map name expr
| (var _) m := m
| (sort _) m := m
| (const _ _) m := m
| (mvar _ _ t) m := contained_lconsts' t m
| lc@(local_const uniq pp bi t) m := contained_lconsts' t (rb_map.insert m uniq lc)
| (app a b) m := contained_lconsts' a (contained_lconsts' b m)
| (lam _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (pi _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (elet _ t v b) m := contained_lconsts' t (contained_lconsts' v (contained_lconsts' b m))
| (macro _ _) m := m

meta def contained_lconsts (e : expr) : rb_map name expr :=
contained_lconsts' e (rb_map.mk name expr)

meta def contained_lconsts_list (es : list expr) : rb_map name expr :=
es.foldl (λ lcs e, contained_lconsts' e lcs) (rb_map.mk name expr)

meta def sort_lconsts : rb_map name expr → list expr | m :=
if m.empty then [] else
let next := m.filter $ λ t, ∀ x ∈ (contained_lconsts t.local_type).keys, ¬ m.contains x in
next.values ++ sort_lconsts (next.fold m (λ n _ m, m.erase n))

meta def mk_pi (lc : expr) (e : expr) : expr :=
expr.pi lc.local_pp_name lc.local_binding_info lc.local_type (e.abstract_local lc.local_uniq_name)

meta def mk_pis : list expr → expr → expr
| (x::xs) e := mk_pi x (mk_pis xs e)
| [] e := e

private def to_const {α} (a : α) : α := a

meta def mk_to_const (n : name) (t : expr) : expr :=
`(@to_const.{1} %%t %%(local_const n n binder_info.default t))

meta mutual def trans_term, trans_type, trans_fml, trans_decl
with trans_term : expr → trans fo_term | t := do
t ← state_t.lift $ zeta t,
t ← state_t.lift $ head_beta t,
t ← state_t.lift $ head_eta t,
is_proof ← state_t.lift (is_proof t),
if is_proof then pure term_prf else
match t with
| `(to_const %%(local_const n pp_n _ _)) :=
  pure $ fo_term.const pp_n
| (app a b) := do
  a' ← trans_term a,
  b' ← trans_term b,
  pure $ fo_term.fn `_A [a', b']
| (const n _) := pure $ fo_term.const n
| (sort _) := pure $ fo_term.const `_S
| (local_const n pp_n _ _) := pure $ fo_term.var pp_n
| (elet pp_n t v b) := trans_term (b.instantiate_var t)
| (mvar _ _ _) := fo_term.const <$> fresh_name `UNSUPPORTED_MVAR
| (macro _ es) :=
  fo_term.fn <$> fresh_name `UNSUPPORTED_MACRO <*> es.mmap trans_term
| (var _) := state_t.lift (fail "open term")
| (lam _ _ _ _) := do
  n ← fresh_name `_lambda,
  ty ← state_t.lift $ infer_type t,
  let lcs := sort_lconsts (contained_lconsts t),
  let n_ty := mk_pis lcs ty,
  let t' := expr.app_of_list (mk_to_const n n_ty) lcs,
  trans_decl n n_ty,
  trans_decl (n.mk_string "eqn") $ mk_pis lcs `(@eq.{1} %%ty %%t %%t'),
  trans_term t'
| (pi _ _ _ _) := do
  n ← fresh_name `_pi,
  ty ← state_t.lift $ infer_type t,
  let lcs := sort_lconsts (contained_lconsts t),
  let n_ty := mk_pis lcs ty,
  let t' := expr.app_of_list (mk_to_const n n_ty) lcs,
  trans_decl n n_ty,
  -- TODO
  -- trans_decl (n.mk_string "eqn") $ mk_pis lcs `(@eq.{1} %%ty %%t %%t'),
  trans_term t'
end
with trans_type : expr → expr → trans fo_fml | e t :=
do t_is_prop ← state_t.lift $ is_prop t,
if t_is_prop then do
  e' ← trans_term e,
  fo_fml.and (fo_fml.eq e' term_prf) <$> trans_fml t
else match t with
| (pi pp_n bi a b) := do
  a_is_prop ← state_t.lift (is_prop a),
  (x', x) ← trans_var pp_n a bi,
  if a_is_prop then do
    a' ← trans_fml a,
    b' ← trans_type (e.app a.mk_sorry) (b.instantiate_var a.mk_sorry),
    pure $ fo_fml.imp a' b'
  else do
    a' ← trans_type x a,
    b' ← trans_type (e.app x) (b.instantiate_var x),
    pure $ fo_fml.all x' $ fo_fml.imp a' b'
| _ := do e' ← trans_term e, t' ← trans_term t, pure (fo_fml.pred `_T [e', t'])
end
with trans_fml : expr → trans fo_fml | t :=
match t with
| `(@eq %%t %%(a@(expr.lam pp_n bi c _)) %%b) := do
  (x, x') ← trans_var pp_n c bi,
  a' ← state_t.lift $ tactic.head_beta $ app a x',
  b' ← state_t.lift $ tactic.head_beta $ app b x',
  t' ← state_t.lift $ infer_type a',
  fo_fml.all x <$> (fo_fml.imp <$> trans_type x' c <*> trans_fml `(@eq.{1} %%t' %%a' %%b'))
| `(@eq %%t %%a %%(b@(expr.lam pp_n bi c _))) := do
  (x, x') ← trans_var pp_n c bi,
  a' ← state_t.lift $ tactic.head_beta $ app a x',
  b' ← state_t.lift $ tactic.head_beta $ app b x',
  t' ← state_t.lift $ infer_type a',
  fo_fml.all x <$> (fo_fml.imp <$> trans_type x' c <*> trans_fml `(@eq.{1} %%t' %%a' %%b'))
| `(@eq %%t %%a %%b) := trans_fml `(@heq.{1} %%t %%t %%a %%b)
| `(@heq %%t %%t' %%a %%b) := do
  t_is_prop ← state_t.lift (is_prop t),
  if t_is_prop then
    trans_fml `(%%a ↔ %%b)
  else
    fo_fml.eq <$> trans_term a <*> trans_term b
| `(%%a ∧ %%b) := fo_fml.and <$> trans_fml a <*> trans_fml b
| `(%%a ∨ %%b) := fo_fml.or <$> trans_fml a <*> trans_fml b
| `(%%a ↔ %%b) := fo_fml.iff <$> trans_fml a <*> trans_fml b
| `(Exists %%(expr.lam pp_n bi a b)) :=
  if b.has_var_idx 0 then do
    (x', x) ← trans_var pp_n a bi,
    a' ← trans_type x a,
    b' ← trans_fml (b.instantiate_var x),
    pure (fo_fml.ex x' $ fo_fml.and a' b')
  else
    fo_fml.and <$> trans_fml a <*> trans_fml b
| (pi pp_n bi a b) :=
  if b.has_var_idx 0 then do
    (x', x) ← trans_var pp_n a bi,
    a' ← trans_type x a,
    b' ← trans_fml (b.instantiate_var x),
    pure (fo_fml.all x' $ fo_fml.imp a' b')
  else
    fo_fml.imp <$> trans_fml a <*> trans_fml b
| _ := do t' ← trans_term t, pure (fo_fml.pred `_P [t'])
end
with trans_decl : name → expr → trans unit | n t := do
t_is_prop ← state_t.lift $ is_prop t,
t' ←
  if t_is_prop then
    trans_fml t
  else
    trans_type (mk_to_const n t) t,
trans.decl_out n t'

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

meta def mk_ignore_args_for_type : expr → list bool
| (expr.pi _ binder_info.inst_implicit t e) := tt :: mk_ignore_args_for_type e
| (expr.pi _ _ bi e) := ff :: mk_ignore_args_for_type e
| _ := []

meta def mk_ignore_args : tactic (rb_map name (list bool)) := do
e ← get_env,
pure $ rb_map.of_list $ e.get_trusted_decls.map $ λ d,
  (d.to_name, mk_ignore_args_for_type d.type)

meta def head_sym_of (e : expr) : name :=
match e.get_app_fn with
| expr.const n _ := n
| _ := name.anonymous
end

meta def non_ignored_consts (il : rb_map name (list bool)) : expr → name_set → name_set
| (expr.pi _ binder_info.inst_implicit t e) := non_ignored_consts e
| (expr.lam _ binder_info.inst_implicit t e) := non_ignored_consts e
| (expr.pi _ _ t e) := non_ignored_consts t ∘ non_ignored_consts e
| (expr.lam _ _ t e) := non_ignored_consts t ∘ non_ignored_consts e
| (expr.var _) := id
| (expr.sort _) := id
| (expr.mvar _ _ _) := id
| (expr.local_const _ _ _ _) := id
| (expr.macro _ es) := λ fv, es.foldl (λ fv e, non_ignored_consts e fv) fv
| (expr.elet _ t v e) := non_ignored_consts t ∘ non_ignored_consts v ∘ non_ignored_consts e
| (expr.const n _) := if is_ignored_const n then id else λ cs, cs.insert n
| e@(expr.app _ _) := λ cs,
let fn := e.get_app_fn, as := e.get_app_args, hs := head_sym_of fn in
let cs := non_ignored_consts fn cs in
(((il.find hs).get_or_else []).zip_extend ff as).foldl
  (λ cs ⟨i, a⟩, if i then cs else non_ignored_consts a cs)
  cs

meta def close_under_instances (ns : list name) : tactic (list name) := do
let ns : rb_set name := rb_map.set_of_list ns,
e ← get_env,
ds ← e.get_trusted_decls.mfilter (λ d, is_instance d.to_name),
il ← mk_ignore_args,
let ds := ds.filter (λ d, ∀ c ∈ (non_ignored_consts il d.type mk_name_set).to_list, ns.contains c),
-- trace $ ds.map (λ d, d.to_name),
pure $ rb_set.to_list $ ds.foldl (λ ns d, ns.insert d.to_name) ns

meta def close_under_equations (ns : list name) : tactic (list name) :=
(list.dup_by_native id ∘ (++ ns) ∘ list.join) <$>
  ns.mmap (λ n, get_eqn_lemmas_for tt n <|> pure [])

meta def trans_decl' (d : declaration) : trans unit := do
t_is_prop ← state_t.lift $ tactic.is_prop d.type,
trans_decl d.to_name d.type,
pure ()
-- when (¬ t_is_prop ∧ d.is_definition) $ do
--   let eqn_ty :=
--     `(@eq.{1} %%d.type %%(expr.const d.to_name (d.univ_params.map level.param)) %%d.value),
--   state_t.lift $ trace eqn_ty,
--   state_t.lift $ infer_type eqn_ty,
--   trans_decl (d.to_name.mk_string "_dfn") eqn_ty

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

meta def add_instance_defeq (i1 i2 : name) : trans unit :=
(do eqn ← state_t.lift $ mk_h_defeq_decl i1 i2,
    n ← fresh_name `_instance_defeq,
    trans_decl n eqn
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
axs ← state_t.lift $ close_under_equations axs,
axs ← state_t.lift $ close_under_references axs,
state_t.lift $ trace $ (axs.map name.to_string).qsort (λ a b, a < b),
axs.mmap' (λ n, do d ← state_t.lift $ get_decl n, trans_decl' d),
add_instance_defeqs axs,
goal_is_prop ← state_t.lift $ tactic.is_prop goal,
goal' ← if goal_is_prop then trans_fml goal
  else (do (x,x') ← trans_var `_goal goal, fo_fml.all x <$> trans_type x' goal),
out ← trans.get_out,
let anns := out.map $ λ ⟨n, f⟩, tptpify_ann "axiom" n f,
let anns := (tptpify_ann "conjecture" `_goal goal') :: anns,
let tptp := format.join $ list.intersperse (format.line ++ format.line) anns.reverse,
pure (tptp, out.map (λ ⟨n, _⟩, (ax_tptpify_name n, n)))

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
axs ← timetac "Premise selection took" $ select_for_goal goal,
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

-- #eval do
-- let goal : expr := `(∀ x y : nat, x < y ∨ x ≥ y),
-- let goal : expr := `(∀ x : nat, x ≤ x),
-- -- axs ← select_for_goal goal,
-- let axs := [(``nat.le_succ, ()), (``le_refl, ())],
-- (tptp, _) ← do_trans ((axs.take 20).map prod.fst) goal,
-- trace tptp

end hammer

namespace tactic

namespace interactive

open interactive interactive.types lean.parser

meta def find_lemmas1 (axs : parse $ optional $ list_of ident) (max_lemmas := 10) : tactic unit := do
goal ← reverted_target,
lems ←
  match axs with
  | none := hammer.find_lemmas1 goal max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "Lemma filtering took" $
      hammer.filter_lemmas1 axs goal
  end,
trace "Vampire proof uses the following lemmas:",
lems.mmap' $ λ l, trace $ "  " ++ l.to_string,
admit

meta def hammer1 (axs : parse $ optional $ list_of ident) (max_lemmas := 10) : tactic unit := do
goal ← reverted_target,
lems ←
  match axs with
  | none := hammer.find_lemmas1 goal max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "Lemma filtering took" $
      hammer.filter_lemmas1 axs goal
  end,
trace "Vampire proof uses the following lemmas:",
lems.mmap' $ λ l, trace $ "  " ++ l.to_string,
tactic.intros,
hammer.reconstruct1 lems

end interactive
end tactic
