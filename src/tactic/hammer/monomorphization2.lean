import tactic.core
tactic.hammer.monomorphization
tactic.hammer.hol
super

local attribute [inline] decidable.to_bool bool.decidable_eq
option.decidable_exists_mem

open native
open expr
open tactic

namespace hammer

meta structure polym_lem :=
(cs : list expr)
(prop : hol_tm)

namespace polym_lem

private meta def c_score : expr → ℕ
| (expr.mvar _ _ _) := 10
| (expr.const ``nonempty _) := 5
| _ := 0

meta def of_hol_tm (thm : hol_tm) : polym_lem := do
let cs := (do c ← thm.exprs, guard c.has_meta_var, pure c),
let cs := cs.dup_native,
let cs := cs.merge_sort (λ a b, c_score a < c_score b),
⟨cs, thm⟩

meta def of_lemma (thm : expr) : tactic polym_lem :=
of_hol_tm <$> hol_tm.of_lemma thm

end polym_lem

meta def monom2_core {α} (cheads : list expr) :
  list expr → tactic (list α) → tactic (list α)
| [] cont := cont
| (e::es) cont := do
  e ← instantiate_mvars e,
  if ¬ e.has_meta_var then monom2_core es cont else
  match e with
  | e@(expr.mvar _ _ _) :=
    -- TODO
    pure []
  | _ := collect_successes (e::cheads) $ λ ch, do
    trace (ch, e),
    unify ch e transparency.reducible,
    monom2_core es cont
  end

meta def monom2 (cheads : list expr) (lem : polym_lem) : tactic (list hol_tm) := do
retrieve_or_else [] $
monom2_core cheads lem.cs $ do
prop ← lem.prop.instantiate_mvars,
guard $ ¬ prop.has_expr_meta_var,
pure [prop]

meta def monomorphization2_round (lems : list polym_lem) : tactic (list hol_tm) := do
let cs := (do l ← lems, c ← l.prop.exprs, guard $ ¬ c.has_meta_var, pure c).dup_native,
lems' ← list.join <$> lems.mmap (monom2 cs),
lems' ← lems'.mmap (λ lem, do t ← lem.to_expr, pure (t, lem)),
let lems' := (lems'.group_by_native prod.fst).to_list.map (λ ⟨k, vs⟩, vs.head.2),
-- trace lems',
-- lems'.mmap infer_type >>= trace,
pure lems'

meta def monomorphize2 (lems : list expr) (rounds := 2) : tactic (list hol_tm) := do
lems ← lems.mmap polym_lem.of_lemma,
rounds.iterate (λ lems', do lems' ← lems',
  monomorphization2_round (lems ++ lems'.map polym_lem.of_hol_tm)) (pure [])

meta def to_tf0.sort_name (e : expr) : to_tf0 string :=
to_tf0.name_core e (λ n, "t" ++ tptpify_name n)

meta mutual def to_tf0_hol_ty, to_tf0_hol_ty_fun
with to_tf0_hol_ty : hol_ty → to_tf0 format
| hol_ty.tbool := pure "$o"
| (hol_ty.base t) := format.of_string <$> to_tf0.sort_name t
| e@(hol_ty.arr _ _) := format.paren' <$> to_tf0_hol_ty_fun e
with to_tf0_hol_ty_fun : hol_ty → to_tf0 format
| (hol_ty.arr a b) := do
  a' ← to_tf0_hol_ty a,
  b' ← to_tf0_hol_ty_fun b,
  pure $ a' ++ format.space ++ ">" ++ format.line ++ b'
| a := to_tf0_hol_ty a

@[pattern] meta def bin_lc (lc : hol_lcon) (a b : hol_tm) : hol_tm :=
hol_tm.app (hol_tm.app (hol_tm.lcon lc) a) b

meta def to_tf0_legalize : hol_tm → tactic hol_tm
| e@(hol_tm.lcon hol_lcon.true) := pure e
| e@(hol_tm.lcon hol_lcon.false) := pure e
| e@(hol_tm.var i) := pure e
| e@(hol_tm.con n _) := pure e
| (bin_lc (hol_lcon.eq t) x y) := bin_lc (hol_lcon.eq t) <$> to_tf0_legalize x <*> to_tf0_legalize y
| (bin_lc hol_lcon.and x y) := bin_lc hol_lcon.and <$> to_tf0_legalize x <*> to_tf0_legalize y
| (bin_lc hol_lcon.or x y) := bin_lc hol_lcon.or <$> to_tf0_legalize x <*> to_tf0_legalize y
| (bin_lc hol_lcon.iff x y) := bin_lc hol_lcon.iff <$> to_tf0_legalize x <*> to_tf0_legalize y
| (bin_lc hol_lcon.imp x y) := bin_lc hol_lcon.imp <$> to_tf0_legalize x <*> to_tf0_legalize y
| (hol_tm.app (hol_tm.lcon hol_lcon.neg) x) := hol_tm.app (hol_tm.lcon hol_lcon.neg) <$> to_tf0_legalize x
| (hol_tm.app (hol_tm.lcon $ hol_lcon.ex t0) (hol_tm.lam x t a)) :=
  (hol_tm.app (hol_tm.lcon $ hol_lcon.ex t0) ∘ hol_tm.lam x t) <$> to_tf0_legalize a
| (hol_tm.app (hol_tm.lcon $ hol_lcon.all t0) (hol_tm.lam x t a)) :=
  (hol_tm.app (hol_tm.lcon $ hol_lcon.all t0) ∘ hol_tm.lam x t) <$> to_tf0_legalize a
| (hol_tm.app a b) := hol_tm.app <$> to_tf0_legalize a <*> to_tf0_legalize b
| (hol_tm.lam x t a) := hol_tm.lam x t <$> to_tf0_legalize a
| (hol_tm.cast t a) := do
  def_eq ← option.is_some <$> try_core (is_def_eq a.ty.to_expr t.to_expr),
  n ← to_expr $
    if def_eq then
      ``(cast rfl : %%a.ty.to_expr → %%t.to_expr)
    else
      ``(cast sorry : %%a.ty.to_expr → %%t.to_expr),
  to_tf0_legalize (hol_tm.app (hol_tm.con n (a.ty.arr t)) a)
| (hol_tm.lcon lc) := do e ← lc.to_expr, to_tf0_legalize $ hol_tm.con e lc.ty

meta def to_tf0_hol_tm : list (name × hol_ty) → hol_tm → to_tf0 format
| lctx (hol_tm.lcon hol_lcon.true) := pure "$true"
| lctx (hol_tm.lcon hol_lcon.false) := pure "$false"
| lctx (hol_tm.var i) :=
  let ⟨n, t⟩ := lctx.inth i in
  format.of_string <$> to_tf0.var_name (expr.local_const n n binder_info.default t.to_expr)
| lctx (hol_tm.con n _) := format.of_string <$> to_tf0.con_name n
| lctx (hol_tm.app (hol_tm.app (hol_tm.lcon $ hol_lcon.eq _) x) y) :=
  tptpify_binop "=" <$> to_tf0_hol_tm lctx x <*> to_tf0_hol_tm lctx y
| lctx (hol_tm.app (hol_tm.app (hol_tm.lcon $ hol_lcon.and) x) y) :=
  tptpify_binop "&" <$> to_tf0_hol_tm lctx x <*> to_tf0_hol_tm lctx y
| lctx (hol_tm.app (hol_tm.app (hol_tm.lcon $ hol_lcon.or) x) y) :=
  tptpify_binop "|" <$> to_tf0_hol_tm lctx x <*> to_tf0_hol_tm lctx y
| lctx (hol_tm.app (hol_tm.app (hol_tm.lcon $ hol_lcon.iff) x) y) :=
  tptpify_binop "<=>" <$> to_tf0_hol_tm lctx x <*> to_tf0_hol_tm lctx y
| lctx (hol_tm.app (hol_tm.app (hol_tm.lcon $ hol_lcon.imp) x) y) :=
  tptpify_binop "=>" <$> to_tf0_hol_tm lctx x <*> to_tf0_hol_tm lctx y
| lctx (hol_tm.app (hol_tm.lcon $ hol_lcon.neg) x) := do
  x' ← to_tf0_hol_tm lctx x,
  pure $ format.paren' $ "~" ++ format.line ++ x'
| lctx (hol_tm.app (hol_tm.lcon $ hol_lcon.ex _) (hol_tm.lam x t a)) := do
  let x' := x.mk_numeral lctx.length,
  tptpify_quant' "?" <$> to_tf0.var_name (expr.local_const x' x' binder_info.default t.to_expr) <*>
    to_tf0_hol_ty t <*> to_tf0_hol_tm ((x', t) :: lctx) a
| lctx (hol_tm.app (hol_tm.lcon $ hol_lcon.all _) (hol_tm.lam x t a)) := do
  let x' := x.mk_numeral lctx.length,
  tptpify_quant' "!" <$> to_tf0.var_name (expr.local_const x' x' binder_info.default t.to_expr) <*>
    to_tf0_hol_ty t <*> to_tf0_hol_tm ((x', t) :: lctx) a
| lctx e@(hol_tm.app _ _) :=
  let fn := e.get_app_fn, as := e.get_app_args in
  (format.paren' ∘ format.join ∘ list.intersperse (format.space ++ "@" ++ format.line))
    <$> (fn :: as).mmap (to_tf0_hol_tm lctx)
| lctx (hol_tm.lam x t a) := do
  let x' := x.mk_numeral lctx.length,
  tptpify_quant' "^" <$> to_tf0.var_name (expr.local_const x' x' binder_info.default t.to_expr) <*>
    to_tf0_hol_ty t <*> to_tf0_hol_tm ((x', t) :: lctx) a
| lctx e := state_t.lift $ do e ← pp e, fail $ to_fmt "to_tf0_hol_tm: unsupported: " ++ e

meta def to_tf0_file2 (lems : list hol_tm) : to_tf0 (format × list (string × hol_tm)) := do
lems ← state_t.lift $ lems.mmap to_tf0_legalize,
let sorts := (lems.map hol_tm.sorts).join.dup_native,
sort_decls ← sorts.mmap (λ c, do
  c' ← to_tf0.sort_name c,
  pure $ tptpify_thf_ann "type" ("ty_" ++ c')
    (tptpify_binop ":" c' "$tType")),
-- state_t.lift $ trace (cs, lems),
let cs := (lems.map hol_tm.consts).join.dup_native,
ty_decls ← cs.mmap (λ ⟨c, t⟩, do
  t' ← to_tf0_hol_ty t,
  c' ← to_tf0.con_name c,
  pure $ tptpify_thf_ann "type" ("ty_" ++ c') (tptpify_binop ":" c' t')),
-- state_t.lift $ trace lems,
axs ← lems.zip_with_index.mmap (λ ⟨ax, i⟩, do
  let n := "ax" ++ to_string i,
  ann ← tptpify_thf_ann "axiom" n <$> to_tf0_hol_tm [] ax,
  pure (n, ax, ann)),
let tptp := format.join $
  ((sort_decls ++ ty_decls ++ axs.map (λ ⟨n,ax,ann⟩, ann)).map format.group)
  .intersperse (format.line ++ format.line),
pure (tptp, axs.map (λ ⟨n,ax,ann⟩, (n, ax)))

meta def mk_monom2_file (axs : list name) : tactic (format × list (string × hol_tm)) := do
goal ← retrieve (revert_all >> target),
let axs := goal.constants.filter is_good_const ++ axs,
axs ← close_under_references axs,
-- trace $ (axs.map name.to_string).qsort (λ a b, a < b),
repeat (intro1 >> skip),
(do tgt ← target, when (tgt ≠ `(false)) $
  mk_mapp ``classical.by_contradiction [some tgt] >>= eapply >> intro1 >> skip),
lems ← (++) <$> axs.mmap mk_const <*> local_context,
lems' ← monomorphize2 lems 2,
-- (cs'', lems'') ← intern_lems lems',
let lems'' := lems',
(to_tf0_file2 lems'').run

-- meta def filter_lemmas2_core (tptp : format) (ax_names : list (string × expr × expr)) :
--   tactic (list (expr × expr)) := do
-- -- trace tptp,
-- (tactic.unsafe_run_io $ do f ← io.mk_file_handle "hammer.p" io.mode.write, io.fs.write f tptp.to_string.to_char_buffer, io.fs.close f),
-- let ax_names := rb_map.of_list ax_names,
-- -- (failure : tactic unit),
-- tptp_out ← timetac "eprover-ho took" $ exec_cmd "bash" ["-c",
--   "set -o pipefail; eprover-ho --cpu-limit=30 --proof-object=1 | " ++
--     "grep -oP '(?<=file\\(..stdin.., ).*?(?=\\))'"]
--   tptp.to_string,
-- let ns := tptp_out.split_on '\n',
-- pure $ do n ← ns, (ax_names.find n).to_list

-- meta def filter_lemmas2 (axs : list name) : tactic (list (expr × expr)) := do
-- (tptp, ax_names) ← mk_monom_file axs,
-- filter_lemmas2_core tptp ax_names

-- meta def find_lemmas2 (max := 10) : tactic (list (expr × expr)) := do
-- axs ← timetac "Premise selection took" $ retrieve $
--   revert_all >> target >>= select_for_goal,
-- let axs := (axs.take max).map (λ a, a.1),
-- -- trace "Premise selection:",
-- trace axs,
-- filter_lemmas2 axs

-- meta def reconstruct2 (axs : list (expr × expr)) : tactic unit :=
-- focus1 $ super.with_ground_mvars $ do
-- axs ← axs.mmap $ λ ⟨pr, ty⟩, super.clause.of_type_and_proof ty pr,
-- super.solve_with_goal {} axs

-- set_option pp.all true
set_option profiler true

example (x y : ℤ) (h : x ∣ y) (h2 : x ≤ y) (h3 : ¬ x + y < 0)
  (h4 : ∃ i : ℤ, i ≤ i + 1) : true := by do
ls ← local_context,
l1 ← mk_const ``add_comm,
l2 ← mk_const ``le_antisymm,
l3 ← mk_const ``exists_congr,
l4 ← mk_const ``add_left_cancel_iff,
let ls : list expr := l1 :: l2 :: l3 :: l4 :: ls,
ls ← ls.mmap infer_type,
-- ls ← (λ x, [x]) <$> get_local `h3,
ls' ← monomorphize2 ls 3,
-- ls'' ← intern_lems ls',
let ls'' := ls',
trace_state,
trace ls'',
-- ls''.mmap' (λ l'', (to_tf0_tm [] l''.2).run >>= trace),
(to_tf0_file2 ls'').run >>= trace,
triv

-- example (x y : ℤ) (h : x ∣ y) (h2 : x ≤ y) (h3 : ¬ x + y < 0) : true :=
-- by feature_search

end hammer

namespace tactic
namespace interactive
open interactive interactive.types lean.parser

-- meta def find_lemmas2 (axs : parse $ optional $ list_of ident) (max_lemmas := 100) : tactic unit := do
-- lems ←
--   match axs with
--   | none := hammer.find_lemmas2 max_lemmas
--   | some axs := do
--     axs.mmap' (λ ax, get_decl ax),
--     timetac "eprover-ho took" $
--       hammer.filter_lemmas2 axs
--   end,
-- trace "eprover-ho proof uses the following lemmas:",
-- lems.mmap' (λ ⟨l, t⟩, do
--   l' ← pp l,
--   -- t ← infer_type l >>= pp,
--   t ← pp t,
--   trace (format.nest 4 $ format.group $ "  " ++ l' ++ " :" ++ format.line ++ t)),
-- admit

-- meta def hammer2 (axs : parse $ optional $ list_of ident) (max_lemmas := 100) : tactic unit := do
-- lems ←
--   match axs with
--   | none := hammer.find_lemmas2 max_lemmas
--   | some axs := do
--     axs.mmap' (λ ax, get_decl ax),
--     timetac "eprover-ho took" $
--       hammer.filter_lemmas2 axs
--   end,
-- trace "eprover-ho proof uses the following lemmas:",
-- lems.mmap' (λ ⟨l, t⟩, do
--   l' ← pp l,
--   -- t ← infer_type l >>= pp,
--   t ← pp t,
--   trace (format.nest 4 $ format.group $ "  " ++ l' ++ " :" ++ format.line ++ t)),
-- hammer.reconstruct2 lems

end interactive
end tactic

-- set_option trace.super true
-- example (x y : ℤ) : x + y = y + x :=
-- by hammer2 [add_comm]
