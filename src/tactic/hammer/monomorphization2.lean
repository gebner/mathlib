import tactic.core
tactic.hammer.monomorphization
tactic.hammer.hol
super

local attribute [inline] decidable.to_bool bool.decidable_eq
option.decidable_exists_mem

meta def tactic.log_exception {α} (tac : tactic α) : tactic α | s :=
match tac s with
| x@(result.exception (some msg) pos st) :=
  (tactic.trace (msg ()) >> (λ _, x) : tactic α) st
| x := x
end

-- meta instance list.has_to_tactic_format {α} [has_to_tactic_format α] : has_to_tactic_format (list α) :=
-- ⟨λ l, to_fmt <$> l.mmap tactic.pp⟩

open native
open expr
open tactic

namespace hammer

meta structure polym_lem :=
(cs : list expr)
(prop : hol_tm)

namespace polym_lem

private meta def c_score : expr → ℕ
| (expr.mvar _ _ _) := 1000
| (expr.const ``nonempty _) := 900
| e := 800 - e.get_weight

meta def of_hol_tm (thm : hol_tm) : polym_lem := do
let cs := (do c ← thm.exprs, guard c.has_meta_var, pure c),
let cs := cs.dup_native,
let cs := cs.merge_sort (λ a b, c_score a < c_score b),
⟨cs, thm⟩

meta def of_lemma (thm : expr) : tactic polym_lem :=
of_hol_tm <$> hol_tm.of_lemma thm

meta def clean_consts (pl : polym_lem) : tactic polym_lem := do
cs ← pl.cs.mmap instantiate_mvars,
let cs := cs.filter (λ e, e.has_meta_var),
pure {cs := cs, ..pl}

end polym_lem

@[reducible] meta def monom3_key := ℕ × expr

meta inductive monom3_fact
| polym_lem (n : expr) (s : tactic_state) (thm : expr) (pl : polym_lem)
| con (c : expr)

namespace monom3_fact

meta def unify : monom3_fact → monom3_fact → list monom3_fact
| (con c') (polym_lem n s thm pl) := do
  c ← pl.cs,
  match c with expr.mvar _ _ _ := [] | _ := pure () end,
  result.success pl' s' ← [(tactic.unify c c' >> pl.clean_consts) s] | [],
  result.success thm' _ ← [instantiate_mvars thm s'] | [],
  [polym_lem n s' thm' pl']
| _ _ := []

meta def key : monom3_fact → monom3_key
| (polym_lem _ _ thm _) := (1, thm)
| (con c) := (0, c)

meta def is_monom : monom3_fact → bool
| (polym_lem n s thm ⟨[], _⟩) := tt
| _ := ff

meta def to_string : monom3_fact → string
| (con c) := "con " ++ c.to_string
| (polym_lem n s thm pl) := (to_fmt "polym_lem " ++ pl.prop.to_format s.fmt_expr).to_string

end monom3_fact

meta def monom3_loop :
  rb_map expr (expr × hol_tm) →
  list monom3_fact →
  rb_map monom3_key monom3_fact →
  rb_map monom3_key monom3_fact → ℕ → list (expr × hol_tm)
| done new active passive n :=
let new_monom := (do
  monom3_fact.polym_lem n s thm ⟨[], tm⟩ ← new | [],
  result.success tm _ ← [tm.instantiate_mvars s] | [],
  [(thm, n, tm)]) in
let new := new.filter (λ f, ¬ f.is_monom) in
let done := new_monom.foldl (λ done x, rb_map.insert done x.1 x.2) done in
if n = 0 then done.values else
let new := new ++ do ⟨_, _, tm⟩ ← new_monom, e ← tm.exprs, [monom3_fact.con e] in
let new := new.filter (λ f, ¬ passive.contains f.key ∧ ¬ active.contains f.key) in
let passive := new.foldl (λ passive x, rb_map.insert passive x.key x) passive in
match passive.min with
| some given :=
  let passive := passive.erase given.key in
  let active := active.insert given.key given in
  let unifs := do a ← active.values, given.unify a ++ a.unify given in
  let unifs := unifs in
  let new := unifs.dup_by_native monom3_fact.key in
  monom3_loop done unifs active passive (n-1)
| none := done.values
end

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
    unify ch e,
    monom2_core es cont
  end

meta def monom2 (cheads : list expr) (lem : (expr × polym_lem)) : tactic (list (expr × hol_tm)) := do
retrieve_or_else [] $
monom2_core cheads lem.2.cs $ do
prop ← lem.2.prop.instantiate_mvars,
guard $ ¬ prop.has_expr_meta_var,
pure [(lem.1, prop)]

meta def monomorphization2_round (lems : list (expr × polym_lem)) : tactic (list (expr × hol_tm)) := do
let cs := (do (n,l) ← lems, c ← l.prop.exprs, guard $ ¬ c.has_meta_var, pure c).dup_native,
lems' ← list.join <$> lems.mmap (monom2 cs),
lems' ← lems'.mmap (λ ⟨n, lem⟩, do t ← lem.to_expr, pure (t, n, lem)),
let lems' := (lems'.dup_by_native prod.fst).map prod.snd,
pure lems'

meta def simplify_lems (lems : list (expr × hol_tm)) (do_canon := tt) : tactic (list (expr × hol_tm)) :=
prod.fst <$> state_t.run (lems.mmap (λ ⟨n, l⟩, prod.mk n <$> l.simplify [])) {do_canon := do_canon}

meta def monomorphize2 (lems : list expr) (rounds := 2) : tactic (list (expr × hol_tm)) := do
lems ← lems.mmap (λ n, prod.mk n <$> (infer_type n >>= hol_tm.of_lemma)),
lems ← simplify_lems lems ff,
let lems := lems.map (λ ⟨n, tm⟩, (n, polym_lem.of_hol_tm tm)),
rounds.iterate (λ lems', do lems' ← lems',
    monomorphization2_round (lems ++
      lems'.map (λ ⟨n,l⟩, prod.mk n (polym_lem.of_hol_tm l))))
  (pure [])

meta def monomorphize3 (lems : list expr) (max_iters := 1000) : tactic (list (expr × hol_tm)) := do
new ← lems.mmap (λ pr, retrieve $ do
  t ← infer_type pr,
  pl ← polym_lem.of_lemma t,
  thm ← pl.prop.to_expr,
  s ← read,
  pure $ monom3_fact.polym_lem pr s thm pl),
pure $ monom3_loop mk_rb_map new mk_rb_map mk_rb_map max_iters

meta def to_tf0.name'_core (e : expr) (t : hol_ty) (f : name → string) : to_tf0 string := do
ns ← to_tf0_state.ns <$> state_t.get,
let e' := `(@id.{1} %%t.to_expr %%e),
match ns.find e' with
| some n := pure n
| none := do
  state_t.modify $ λ st, { fresh_idx := st.fresh_idx + 1, ..st },
  idx ← to_tf0_state.fresh_idx <$> state_t.get,
  let n := f (name.mk_numeral (unsigned.of_nat idx) (hint_name e)),
  state_t.modify $ λ st, { ns := st.ns.insert e' n, ..st },
  pure n
end

meta def to_tf0.var_name' (n : name) (t : hol_ty) : to_tf0 string :=
to_tf0.name'_core (expr.local_const n n binder_info.default t.to_expr) t var_tptpify_name

meta def to_tf0.con_name' (e : expr) (t : hol_ty) : to_tf0 string :=
to_tf0.name'_core e t fn_tptpify_name

meta def to_tf0.ax_name' (e : expr) : to_tf0 string :=
to_tf0.name'_core e hol_ty.tbool ax_tptpify_name

meta def to_tf0.sort_name' (e : expr) : to_tf0 string :=
to_tf0.name'_core e hol_ty.tbool (λ n, "t" ++ tptpify_name n)

meta mutual def to_tf0_hol_ty, to_tf0_hol_ty_fun
with to_tf0_hol_ty : hol_ty → to_tf0 format
| hol_ty.tbool := pure "$o"
| (hol_ty.base t) := format.of_string <$> to_tf0.sort_name' t
| e@(hol_ty.arr _ _) := format.paren' <$> to_tf0_hol_ty_fun e
with to_tf0_hol_ty_fun : hol_ty → to_tf0 format
| (hol_ty.arr a b) := do
  a' ← to_tf0_hol_ty a,
  b' ← to_tf0_hol_ty_fun b,
  pure $ a' ++ format.space ++ ">" ++ format.line ++ b'
| a := to_tf0_hol_ty a

@[pattern] meta def bin_lc (lc : hol_lcon) (a b : hol_tm) : hol_tm :=
hol_tm.app (hol_tm.app (hol_tm.lcon lc) a) b

meta def to_tf0_bailout : hol_tm → list hol_ty → tactic hol_tm
| e [] := do e' ← e.to_expr, pure (hol_tm.con e' e.ty)
| e (t::lctx) :=
  if ¬ e.has_var_idx 0 then do
    e' ← to_tf0_bailout (e.instantiate_var (hol_tm.var 0)) lctx,
    pure $ e'.lift_core 1 0
  else do
    l ← mk_local' `x binder_info.default t.to_expr,
    let l' := hol_tm.con l t,
    e' ← to_tf0_bailout (hol_tm.lam `x t e) lctx,
    pure $ (e'.lift_core 1 0).app (hol_tm.var 0)

meta def to_tf0_legalize : hol_tm → list hol_ty → tactic hol_tm
| e@(hol_tm.lcon hol_lcon.true) lctx := pure e
| e@(hol_tm.lcon hol_lcon.false) lctx := pure e
| e@(hol_tm.var i) lctx := pure e
| e@(hol_tm.con n _) lctx := pure e
| (bin_lc (hol_lcon.eq t) x y) lctx := bin_lc (hol_lcon.eq t) <$> to_tf0_legalize x lctx <*> to_tf0_legalize y lctx
| (bin_lc hol_lcon.and x y) lctx := bin_lc hol_lcon.and <$> to_tf0_legalize x lctx <*> to_tf0_legalize y lctx
| (bin_lc hol_lcon.or x y) lctx := bin_lc hol_lcon.or <$> to_tf0_legalize x lctx <*> to_tf0_legalize y lctx
| (bin_lc hol_lcon.iff x y) lctx := bin_lc hol_lcon.iff <$> to_tf0_legalize x lctx <*> to_tf0_legalize y lctx
| (bin_lc hol_lcon.imp x y) lctx := bin_lc hol_lcon.imp <$> to_tf0_legalize x lctx <*> to_tf0_legalize y lctx
| (hol_tm.app (hol_tm.lcon hol_lcon.neg) x) lctx := hol_tm.app (hol_tm.lcon hol_lcon.neg) <$> to_tf0_legalize x lctx
| (hol_tm.app (hol_tm.lcon $ hol_lcon.ex t0) (hol_tm.lam x t a)) lctx :=
  (hol_tm.app (hol_tm.lcon $ hol_lcon.ex t0) ∘ hol_tm.lam x t) <$> to_tf0_legalize a (t :: lctx)
| (hol_tm.app (hol_tm.lcon $ hol_lcon.all t0) (hol_tm.lam x t a)) lctx :=
  (hol_tm.app (hol_tm.lcon $ hol_lcon.all t0) ∘ hol_tm.lam x t) <$> to_tf0_legalize a (t :: lctx)
| (hol_tm.app a b) lctx := hol_tm.app <$> to_tf0_legalize a lctx <*> to_tf0_legalize b lctx
| e@(hol_tm.lam x t a) lctx :=
  to_tf0_bailout e lctx
  -- hol_tm.lam x t <$> to_tf0_legalize a (t :: lctx)
| (hol_tm.cast t a) lctx := do
  let ta := a.ty_core lctx,
  n ← to_expr ``(cast sorry : %%ta.to_expr → %%t.to_expr),
  to_tf0_legalize (hol_tm.app (hol_tm.con n (ta.arr t)) a) lctx
| (hol_tm.lcon lc) lctx := do e ← lc.to_expr, to_tf0_legalize (hol_tm.con e lc.ty) lctx

meta def to_tf0_hol_tm : list (name × hol_ty) → hol_tm → to_tf0 format
| lctx (hol_tm.lcon hol_lcon.true) := pure "$true"
| lctx (hol_tm.lcon hol_lcon.false) := pure "$false"
| lctx (hol_tm.var i) :=
  let ⟨n, t⟩ := lctx.inth i in
  format.of_string <$> to_tf0.var_name' n t
| lctx (hol_tm.con n t) := format.of_string <$> to_tf0.con_name' n t
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
  tptpify_quant' "?" <$> to_tf0.var_name' x' t <*>
    to_tf0_hol_ty t <*> to_tf0_hol_tm ((x', t) :: lctx) a
| lctx (hol_tm.app (hol_tm.lcon $ hol_lcon.all _) (hol_tm.lam x t a)) := do
  let x' := x.mk_numeral lctx.length,
  tptpify_quant' "!" <$> to_tf0.var_name' x' t <*>
    to_tf0_hol_ty t <*> to_tf0_hol_tm ((x', t) :: lctx) a
| lctx e@(hol_tm.app _ _) :=
  let fn := e.get_app_fn, as := e.get_app_args in
  (format.paren' ∘ format.join ∘ list.intersperse (format.space ++ "@" ++ format.line))
    <$> (fn :: as).mmap (to_tf0_hol_tm lctx)
| lctx (hol_tm.lam x t a) := do
  let x' := x.mk_numeral lctx.length,
  tptpify_quant' "^" <$> to_tf0.var_name' x' t <*>
    to_tf0_hol_ty t <*> to_tf0_hol_tm ((x', t) :: lctx) a
| lctx e := state_t.lift $ do e ← pp e, fail $ to_fmt "to_tf0_hol_tm: unsupported: " ++ e

meta def prefix_with_fmt_comment (e : format) (f : format) : to_tf0 format := do
let e' := e.to_string (options.mk.set_nat `pp.width 1000000),
pure $ to_fmt ("% " ++ e') ++ "\n" ++ f

meta def prefix_with_expr_comment (e : expr) (f : format) : to_tf0 format := do
e' ← state_t.lift $ pp e,
prefix_with_fmt_comment e' f

meta def prefix_with_expr_ty_comment (e : expr) (ty : expr) (f : format) : to_tf0 format := do
e' ← state_t.lift $ pp e,
ty' ← state_t.lift $ pp ty,
prefix_with_fmt_comment (e' ++ " : " ++ ty') f

meta def to_tf0_file2 (lems : list (expr × hol_tm)) : to_tf0 (format × list (string × expr × hol_tm)) := do
lems ← state_t.lift $ lems.mmap $ λ ⟨n, l⟩, prod.mk n <$> to_tf0_legalize l [],
let sorts := (lems.map (hol_tm.sorts ∘ prod.snd)).join.dup_native,
sort_decls ← sorts.mmap (λ c, do
  c' ← to_tf0.sort_name' c,
  prefix_with_expr_comment c $
    tptpify_thf_ann "type" ("ty_" ++ c')
      (tptpify_binop ":" c' "$tType")),
let cs := (lems.map (hol_tm.consts ∘ prod.snd)).join.dup_native,
ty_decls ← cs.mmap (λ ⟨c, t⟩, do
  t' ← to_tf0_hol_ty t,
  c' ← to_tf0.con_name' c t,
  prefix_with_expr_ty_comment c t.to_expr $
    tptpify_thf_ann "type" ("ty_" ++ c') (tptpify_binop ":" c' t')),
axs ← lems.mmap (λ ⟨pr, ax⟩, do
  n ← to_tf0.ax_name' pr,
  ann ← tptpify_thf_ann "axiom" n <$> to_tf0_hol_tm [] ax,
  ax' ← state_t.lift $ pp ax,
  ann ← prefix_with_fmt_comment ax' ann,
  pure (n, pr, ax, ann)),
let tptp := format.join $
  ((sort_decls ++ ty_decls ++ axs.map (λ ⟨n,pr,ax,ann⟩, ann)).map format.group)
  .intersperse (format.line ++ format.line),
pure (tptp, axs.map (λ ⟨n,pr,ax,ann⟩, (n, pr, ax)))

meta def mk_monom2_file (axs : list name) : tactic (format × list (string × expr × hol_tm)) := do
goal ← retrieve (revert_all >> target),
let axs := goal.constants.filter is_good_const ++ axs,
axs ← close_under_references axs,
repeat (intro1 >> skip),
(do tgt ← target, when (tgt ≠ `(false)) $
  mk_mapp ``classical.by_contradiction [some tgt] >>= eapply >> intro1 >> skip),
lems ← (++) <$> axs.mmap mk_const <*> local_context,
lems' ← monomorphize2 lems,
lems'' ← simplify_lems lems',
(to_tf0_file2 lems'').run

meta def filter_lemmas3_core (tptp : format) (ax_names : list (string × expr × hol_tm)) :
  tactic (list (expr × hol_tm)) := do
trace tptp,
(tactic.unsafe_run_io $ do f ← io.mk_file_handle "hammer.p" io.mode.write, io.fs.write f tptp.to_string.to_char_buffer, io.fs.close f),
let ax_names := rb_map.of_list ax_names,
-- (failure : tactic unit),
tptp_out ← timetac "eprover-ho took" $ exec_cmd "bash" ["-c",
  "set -o pipefail; eprover-ho --cpu-limit=30 --proof-object=1 | " ++
    "grep -oP '(?<=file\\(..stdin.., ).*?(?=\\))'"]
  tptp.to_string,
let ns := tptp_out.split_on '\n',
pure $ do n ← ns, (ax_names.find n).to_list

meta def filter_lemmas3 (axs : list name) : tactic (list (expr × hol_tm)) := do
(tptp, ax_names) ← mk_monom2_file axs,
filter_lemmas3_core tptp ax_names

meta def find_lemmas3 (max := 10) : tactic (list (expr × hol_tm)) := do
axs ← timetac "Premise selection took" $ retrieve $
  revert_all >> target >>= select_for_goal,
let axs := (axs.take max).map (λ a, a.1),
-- trace "Premise selection:",
trace axs,
filter_lemmas3 axs

meta def reconstruct3 (axs : list (expr × hol_tm)) : tactic unit :=
focus1 $ super.with_ground_mvars $ do
axs ← axs.mmap $ λ ⟨pr, _⟩, super.clause.of_proof pr,
super.solve_with_goal {} axs

-- set_option pp.all true
-- set_option profiler true
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

example (x y : ℤ) (h : x ∣ y) (h2 : x ≤ y) (h3 : ¬ x + y < 0)
  (h4 : ∃ i : ℤ, i ≤ i + 1) : true := by do
ls ← local_context,
l1 ← mk_const ``add_comm,
l2 ← mk_const ``le_antisymm,
l3 ← mk_const ``exists_congr,
l4 ← mk_const ``zero_sub,
let ls : list expr := l1 :: l2 :: l3 :: l4 :: ls,
-- ls ← (λ x, [x]) <$> get_local `h3,
ls ← monomorphize2 ls,
ls ← simplify_lems ls,
trace ls,
-- ls''.mmap' (λ l'', (to_tf0_tm [] l''.2).run >>= trace),
(to_tf0_file2 ls).run >>= trace,
triv

-- example (x y : ℤ) (h : x ∣ y) (h2 : x ≤ y) (h3 : ¬ x + y < 0) : true :=
-- by feature_search

end hammer

namespace tactic
namespace interactive
open interactive interactive.types lean.parser

meta def find_lemmas3 (axs : parse $ optional $ list_of ident) (max_lemmas := 100) : tactic unit := do
lems ←
  match axs with
  | none := hammer.find_lemmas3 max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "eprover-ho took" $
      hammer.filter_lemmas3 axs
  end,
trace "eprover-ho proof uses the following lemmas:",
lems.mmap' (λ ⟨l, t⟩, do
  l' ← pp l,
  -- t ← infer_type l >>= pp,
  t ← pp t,
  trace (format.nest 4 $ format.group $ "  " ++ l' ++ " :" ++ format.line ++ t)),
admit

meta def hammer3 (axs : parse $ optional $ list_of ident) (max_lemmas := 100) : tactic unit := do
lems ←
  match axs with
  | none := hammer.find_lemmas3 max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "eprover-ho took" $
      hammer.filter_lemmas3 axs
  end,
trace "eprover-ho proof uses the following lemmas:",
lems.mmap' (λ ⟨l, t⟩, do
  l' ← pp l,
  -- t ← infer_type l >>= pp,
  t ← pp t,
  trace (format.nest 4 $ format.group $ "  " ++ l' ++ " :" ++ format.line ++ t)),
hammer.reconstruct3 lems

end interactive
end tactic

-- set_option trace.super true
-- set_option profiler true
-- example (x y : ℤ) : x + y = y + x :=
-- by hammer3 20
