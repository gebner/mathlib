import tactic.core
tactic.hammer.fo_translation
super

local attribute [inline] decidable.to_bool bool.decidable_eq
option.decidable_exists_mem

open native

meta def list.dup_native {α} [has_lt α] [decidable_rel ((<) : α → α → Prop)] (xs : list α) : list α :=
rb_set.to_list $ rb_map.set_of_list xs

meta def list.group_by_native {α β} [has_lt α] [decidable_rel ((<) : α → α → Prop)] (xs : list β) (f : β → α) : rb_map α (list β) :=
xs.foldl (λ m x, m.insert (f x) (x :: (m.find (f x)).get_or_else [])) mk_rb_map

open expr

meta def expr.app_short (a b : expr) : expr :=
match a with
| (lam _ _ _ a) := a.instantiate_var b
| _ := app a b
end

meta def level.has_mvar : level → bool
| (level.param _) := ff
| (level.succ l) := l.has_mvar
| (level.mvar _) := tt
| level.zero := ff
| (level.max l1 l2) := l1.has_mvar ∨ l2.has_mvar
| (level.imax l1 l2) := l1.has_mvar ∨ l2.has_mvar

meta def expr.has_level_mvar : expr → bool
| (var _) := ff
| (mvar _ _ t) := t.has_level_mvar
| (sort l) := l.has_mvar
| (macro _ es) := es.any expr.has_level_mvar
| (app a b) := a.has_level_mvar ∨ b.has_level_mvar
| (expr.const _ ls) := ls.any level.has_mvar
| (expr.local_const _ _ _ t) := t.has_level_mvar
| (pi _ _ a b) := a.has_level_mvar ∨ b.has_level_mvar
| (lam _ _ a b) := a.has_level_mvar ∨ b.has_level_mvar
| (elet _ a b c) := a.has_level_mvar ∨ b.has_level_mvar ∨ c.has_level_mvar

meta def expr.consts_and_local_consts_core : expr → rb_set expr → rb_set expr
| (var _) := id
| (mvar _ _ _) := id
| (sort _) := id
| (macro _ es) := λ s, es.foldl (λ s e, e.consts_and_local_consts_core s) s
| (app a b) := a.consts_and_local_consts_core ∘ b.consts_and_local_consts_core
| e@(expr.const _ _) := if e.has_level_mvar then id else λ s, s.insert e
| e@(expr.local_const _ _ _ t) := if t.has_var ∨ t.has_level_mvar then id else λ s, s.insert e
| (pi _ _ a b) := a.consts_and_local_consts_core ∘ b.consts_and_local_consts_core
| (lam _ _ a b) := a.consts_and_local_consts_core ∘ b.consts_and_local_consts_core
| (elet _ a b c) :=
  a.consts_and_local_consts_core ∘ b.consts_and_local_consts_core
    ∘ c.consts_and_local_consts_core

meta def consts_and_local_consts (es : list expr) : list expr :=
rb_set.to_list $ es.foldl (λ s e, e.consts_and_local_consts_core s) mk_rb_set

meta def tactic.retrieve_or_else {α} (a : α) (tac : tactic α) : tactic α :=
λ s, result.cases_on (tac s)
  (λ a _, result.success a s)
  (λ _ _ _, result.success a s)

meta def tactic.collect_successes {α β} (as : list α) (tac : α → tactic (list β)) : tactic (list β) :=
list.join <$> as.mmap (λ a, tactic.retrieve_or_else [] (tac a))

meta def mk_lam (lc : expr) (e : expr) : expr :=
expr.lam lc.local_pp_name lc.local_binding_info lc.local_type (e.abstract_local lc.local_uniq_name)

open tactic

meta def tactic.is_type (e : expr) : tactic bool := do
e ← whnf e,
match e with
| (sort _) := pure tt
| _ := pure ff
end

namespace hammer

open expr tactic

meta def get_head_name : expr → name
| (app a _) := get_head_name a
| (local_const uniq_name _ _ _) := uniq_name
| (const n _) := n
| _ := name.anonymous

meta def hint_name : expr → name
| (app a _) := hint_name a
| (lam _ _ _ a) := hint_name a
| (local_const _ (name.mk_string n _) _ _) := n
| (local_const un (name.mk_numeral _ n) bi t) := hint_name (local_const un n bi t)
| (const (name.mk_string n _) _) := n
| (const _ _) := `c
| _ := `x

meta def num_mono_args : expr → ℕ
| (expr.pi pp_n bi d t) :=
  let n' := num_mono_args t in
  if n' > 0 then
    n' + 1
  else if t.has_var_idx 0 ∨ bi = binder_info.inst_implicit then
    1
  else
    0
| _ := 0

-- #eval (num_mono_args <$> infer_type `(@has_add.add.{0})) >>= trace

meta def gather_constant_heads (nargs : rb_map name ℕ) : expr → list expr
| (lam _ _ d e) := gather_constant_heads d ++ gather_constant_heads e
| (pi _ _ d e) := gather_constant_heads d ++ gather_constant_heads e
| (elet _ a b c) := gather_constant_heads a ++ gather_constant_heads b ++ gather_constant_heads c
| e :=
let fn := e.get_app_fn, as := e.get_app_args in
let acc := if as = [] then [] else gather_constant_heads fn ++ as.bind gather_constant_heads in
match nargs.find (get_head_name fn) with
| some n :=
  let ch := mk_app fn (as.take n) in
  if n ≤ as.length ∧ ¬ ch.has_var then ch :: acc else acc
| none := acc
end

meta def monom_core {α} (nargs : rb_map name ℕ) (cheads : rb_map name (list expr)) :
  expr → tactic (list α) → tactic (list α)
| (lam _ _ d e) cont := monom_core d $ monom_core e $ cont
| (pi _ _ d e) cont := monom_core d $ monom_core e $ cont
| (elet _ a b c) cont := monom_core a $ monom_core b $ monom_core c $ cont
| e cont :=
-- if ¬ e.has_meta_var ∧ ¬ e.has_level_mvar then cont else
let fn := e.get_app_fn, fnn := get_head_name fn, as := e.get_app_args in
-- do trace fn, trace nargs, trace cheads,
match (nargs.find fnn, cheads.find fnn) with
| (some n, some chs) := do
  e' ← instantiate_mvars $ mk_app fn (as.take n),
  -- trace (e, n, chs),
  if ¬ e'.has_meta_var ∧ ¬ e'.has_level_mvar then
    (as.drop n).foldl (λ cont a, monom_core a cont) cont
  else do
    res1 ← (collect_successes chs $ λ ch, do
      -- trace (ch, e'),
      unify ch e',
      (as.drop n).foldl (λ cont a, monom_core a cont) cont),
    -- trace res1.length,
    res2 ← retrieve_or_else [] $
      (as.drop n).foldl (λ cont a, monom_core a cont) cont,
    pure $ res1 ++ res2
| _ :=
  if as = [] then cont else
  (fn :: as : list expr).foldl (λ cont a, monom_core a cont) cont
end

meta def monom' (nargs : rb_map name ℕ) (cheads : rb_map name (list expr)) :
  expr → expr → (expr → tactic expr) → tactic (list expr)
| (pi n bi d ty) prf cont := do
  m ← mk_meta_var d,
  monom' (ty.instantiate_var m) (prf.app_short m) $ λ prf, do
    try $ mk_instance d >>= unify m,
    m ← instantiate_mvars m,
    match m with
    | (mvar _ _ _) := do
      l ← mk_local' n bi d,
      unify m l,
      prf ← instantiate_mvars prf,
      cont $ mk_lam l prf
    | _ := cont prf
    end
| ty prf cont :=
-- do trace ty,
  monom_core nargs cheads ty $ (λ x, [x]) <$> cont prf

meta def monom (nargs : rb_map name ℕ) (cheads : rb_map name (list expr))
  (prf : expr) : tactic (list expr) := do
ty ← infer_type prf,
retrieve_or_else [] $
monom' nargs cheads ty prf $ λ prf, do
prf ← instantiate_mvars prf,
guard $ ¬ prf.has_meta_var,
guard $ ¬ prf.has_level_mvar,
pure prf

meta def monomorphization_round (lems : list expr) : tactic (list expr) := do
cs ← _root_.consts_and_local_consts <$> lems.mmap infer_type,
-- trace cs,
nargs ← rb_map.of_list <$> cs.mmap (λ c, do t ← infer_type c, pure (get_head_name c, num_mono_args t)),
-- trace nargs,
cheads ← lems.mmap (λ lem, gather_constant_heads nargs <$> infer_type lem),
let cheads := (cheads.join.group_by_native get_head_name).map list.dup_native,
-- trace cheads,
lems' ← lems.mmap $ λ lem, monom nargs cheads lem,
lems' ← lems'.join.mmap (λ lem, do t ← infer_type lem, pure (t, lem)),
let lems' := (lems'.group_by_native prod.fst).to_list.map (λ ⟨k, vs⟩, vs.head.2),
let lems' := lems'.dup_native,
-- trace lems',
-- lems'.mmap infer_type >>= trace,
pure lems'

meta def monomorphize (lems : list expr) (rounds := 2) : tactic (list expr) := do
mon ← rounds.iterate (λ lems', do lems' ← lems', monomorphization_round (lems ++ lems')) (pure []),
pure (lems ++ mon).dup_native

meta structure intern_state :=
(fresh_idx : ℕ := 0)
(nfs : list expr := [])
(nargs : rb_map name ℕ)

@[reducible]
meta def intern := state_t intern_state tactic

meta def tactic_mfind {α} (tac : α → tactic unit) : list α → tactic α
| [] := failed
| (h::t) := tac h >> return h <|> tactic_mfind t

meta def intern.fresh_num : intern ℕ := do
state_t.modify (λ s, { fresh_idx := s.fresh_idx + 1, ..s }),
intern_state.fresh_idx <$> state_t.get

meta def intern.fresh_name (hint : name) : intern name :=
do n ← intern.fresh_num, pure $ name.mk_numeral (unsigned.of_nat n) hint

meta def intern_here : ∀ (lctx : list expr) (e : expr), intern expr
| _ e@(const _ []) := pure e
| _ e@(local_const _ _ _ _) := pure e
| (lc :: lctx) e :=
  let e' := e.abstract_local lc.local_uniq_name in
  if ¬ e'.has_var then intern_here lctx e else do
  e'' ← intern_here lctx (lam lc.local_pp_name binder_info.default lc.local_type e'),
  -- this is wrong
  pure (e'' lc)
| [] e := do
  nfs ← intern_state.nfs <$> state_t.get,
  nf ← state_t.lift $ try_core $ first $ nfs.map (λ nf, do is_def_eq e nf, pure nf),
  match nf with
  | some nf := pure nf
  | _ := do
    n ← intern.fresh_name (hint_name e),
    -- state_t.lift $ trace (n,e),
    c ← state_t.lift $ pose n none e,
    state_t.modify $ λ st, { nfs := c :: nfs, ..st },
    pure c
  end

meta def get_nargs (e : expr) : intern (option ℕ) := do
nargs ← intern_state.nargs <$> state_t.get,
pure (nargs.find (get_head_name e))

meta def intern_ty (lctx : list expr) : expr → intern expr
| t@(sort level.zero) := pure t
| e@(pi pp_n bi d t) :=
  if t.has_var then intern_here [] e else
  imp <$> intern_ty d <*> intern_ty t
| `(out_param %%t) := intern_ty t
| `(auto_param %%t _) := intern_ty t
| `(opt_param %%t _) := intern_ty t
| e := intern_here lctx e

meta def intern_expr : list expr → expr → intern expr
| lctx `(%%a = %%b) := do
  a ← intern_expr lctx a,
  b ← intern_expr lctx b,
  state_t.lift $ mk_app ``eq [a,b]
| lctx e@(app (app (const ``Exists ls) α) (lam pp_n bi _ p)) := do
  a_type ← state_t.lift $ is_type α,
  a_prop ← state_t.lift $ is_prop α,
  if ¬ a_type ∧ ¬ a_prop then do
    α ← intern_ty lctx α,
    lc ← state_t.lift $ mk_local' pp_n bi α,
    p ← intern_expr lctx (p.instantiate_var lc),
    pure $ app (const ``Exists ls) α
      (lam pp_n bi α (p.abstract_local lc.local_uniq_name))
  else
    intern_here lctx e
| lctx (app (app (const ``Exists ls) α) p) :=
  -- η-expand
  intern_expr lctx (app (const ``Exists ls)
    α (lam `x binder_info.default α (p (var 0))))
| lctx e@(app a b) := do
  nargs ← get_nargs e,
  if ∃ n ∈ nargs, n ≥ e.get_app_num_args then intern_here lctx e else do
  ta ← state_t.lift $ infer_type a >>= whnf,
  let is_dep := match ta with
    | (expr.pi _ _ _ t) := t.has_var
    | _ := tt
    end,
  if is_dep then intern_here lctx e else app <$> intern_expr lctx a <*> intern_expr lctx b
| lctx e@(pi pp_n bi d t0) := do
  lc ← state_t.lift $ mk_local' pp_n bi d,
  let t := t0.instantiate_var lc,
  t_prop ← state_t.lift $ is_prop t,
  d_prop ← state_t.lift $ is_prop d,
  d_type ← state_t.lift $ is_type d,
  if t_prop ∧ d_prop ∧ ¬ t0.has_var then -- implication
    imp <$> intern_expr lctx d <*> intern_expr lctx t
  else if t_prop ∧ ¬ d_prop ∧ ¬ d_type then do -- forall
    d ← intern_ty lctx d,
    t ← intern_expr (lc :: lctx) t,
    pure (pi pp_n binder_info.default d (t.abstract_local lc.local_uniq_name))
  else
    intern_here lctx e
| lctx e@(lam pp_n bi d t) := do
  d_type ← state_t.lift $ is_type d,
  if ¬ d_type ∧ false then do
    lc ← state_t.lift $ mk_local' pp_n bi d,
    let t := t.instantiate_var lc,
    -- t_prop ← state_t.lift $ is_prop t,
    -- if ¬ t_prop then intern_here lctx e else do
    d ← intern_ty lctx d,
    t ← intern_expr (lc :: lctx) t,
    pure (lam pp_n binder_info.default d (t.abstract_local lc.local_uniq_name))
  else
    intern_here lctx e
| lctx e := intern_here lctx e

meta def intern_lems (lems : list expr) : tactic (list (expr × expr) × list (expr × expr)) := do
lems ← lems.mfilter is_proof,
tys ← lems.mmap infer_type,
let cs := _root_.consts_and_local_consts tys,
nargs ← rb_map.of_list <$> cs.mmap (λ c, do t ← infer_type c, pure (get_head_name c, num_mono_args t)),
prod.fst <$> state_t.run (do
lems' ← lems.mmap (λ l, do
      t ← state_t.lift (infer_type l),
      t ← intern_expr [] t,
      pure (l, t)),
let cs := _root_.consts_and_local_consts (lems'.map prod.snd),
cs' ← cs.mmap (λ c, do
      t ← state_t.lift (infer_type c),
      t ← intern_ty [] t,
      pure (c,t)),
pure $ (cs', lems')) { nargs := nargs }

meta def tptpify_quant' (q : string) (x : string) (t : format) (b : format) : format :=
format.paren' $ q ++ (format.nest 1 $ format.group $
  "[" ++ x ++ ":" ++ format.line ++ t ++ "]:") ++ format.line ++ b

meta structure to_tf0_state :=
(fresh_idx := 0)
(ns : rb_map expr string := mk_rb_map)

@[reducible] meta def to_tf0 := state_t to_tf0_state tactic

meta def to_tf0.name_core (e : expr) (f : name → string) : to_tf0 string := do
ns ← to_tf0_state.ns <$> state_t.get,
match ns.find e with
| some n := pure n
| none := do
  state_t.modify $ λ st, { fresh_idx := st.fresh_idx + 1, ..st },
  idx ← to_tf0_state.fresh_idx <$> state_t.get,
  let n := match e with
    | (const n _) := f n
    | _ := f (name.mk_numeral (unsigned.of_nat idx) (hint_name e))
    end,
  state_t.modify $ λ st, { ns := st.ns.insert e n, ..st },
  pure n
end

meta def to_tf0.var_name (e : expr) : to_tf0 string :=
to_tf0.name_core e var_tptpify_name

meta def to_tf0.con_name (e : expr) : to_tf0 string :=
to_tf0.name_core e fn_tptpify_name

meta def to_tf0.ax_name (e : expr) : to_tf0 string :=
to_tf0.name_core e ax_tptpify_name

meta mutual def to_tf0_ty, to_tf0_ty_fun
with to_tf0_ty : expr → to_tf0 format
| (sort level.zero) := pure "$o"
| lc@(local_const _ _ _ _) :=
  format.of_string <$> to_tf0.con_name lc
| c@(const n _) := format.of_string <$> to_tf0.con_name c
| e@(pi _ _ _ _) := format.paren' <$> to_tf0_ty_fun e
| e := do state_t.lift $ trace e, pure "e_UNSUPPORTED"
with to_tf0_ty_fun : expr → to_tf0 format
| (pi _ _ a b) := do
  a' ← to_tf0_ty a,
  b' ← to_tf0_ty_fun b,
  pure $ a' ++ format.space ++ ">" ++ format.line ++ b'
| a := to_tf0_ty a

meta def to_tf0_tm : list expr → expr → to_tf0 format
| lctx `(true) := pure "$true"
| lctx `(false) := pure "$false"
| lctx lc@(local_const _ _ _ _) :=
  format.of_string <$> if lc ∈ lctx then to_tf0.var_name lc else to_tf0.con_name lc
| lctx (const n _) := pure $ fn_tptpify_name n
| lctx `(%%x = %%y) := tptpify_binop "=" <$> to_tf0_tm lctx x <*> to_tf0_tm lctx y
| lctx `(%%x ∧ %%y) := tptpify_binop "&" <$> to_tf0_tm lctx x <*> to_tf0_tm lctx y
| lctx `(%%x ∨ %%y) := tptpify_binop "|" <$> to_tf0_tm lctx x <*> to_tf0_tm lctx y
| lctx `(%%x ↔ %%y) := tptpify_binop "<=>" <$> to_tf0_tm lctx x <*> to_tf0_tm lctx y
| lctx `(¬ %%x) := do
  x' ← to_tf0_tm lctx x,
  pure $ format.paren' $ "~" ++ format.line ++ x'
| lctx (app (app (const ``Exists α) _) (lam pp_n _ d a)) := do
  lc ← state_t.lift $ mk_local' pp_n binder_info.default d,
  tptpify_quant' "?" <$> to_tf0.var_name lc <*> to_tf0_ty d <*>
    to_tf0_tm (lc :: lctx) (a.instantiate_var lc)
| lctx e@(pi pp_n _ d a) := do
  d_is_prop ← state_t.lift $ is_prop d,
  if ¬ d_is_prop then do
    lc ← state_t.lift $ mk_local' pp_n binder_info.default d,
    let a' := a.instantiate_var lc,
    tptpify_quant' "!" <$> to_tf0.var_name lc <*> to_tf0_ty d <*> to_tf0_tm (lc :: lctx) a'
  else
    if a.has_var then do
      state_t.lift $ trace e, pure "e_UNSUPPORTED"
    else
      tptpify_binop "=>" <$> to_tf0_tm lctx d <*> to_tf0_tm lctx a
| lctx e@(app _ _) :=
  let fn := e.get_app_fn, as := e.get_app_args in
  (format.paren' ∘ format.join ∘ list.intersperse (format.space ++ "@" ++ format.line))
    <$> (fn :: as).mmap (to_tf0_tm lctx)
-- | lctx (app a b) := tptpify_binop "@" <$> to_tf0_tm lctx a <*> to_tf0_tm lctx b
| lctx (lam pp_n bi d a) := do
  lc ← state_t.lift $ mk_local' pp_n binder_info.default d,
  tptpify_quant' "^" <$> to_tf0.var_name lc <*> to_tf0_ty d <*>
    to_tf0_tm (lc :: lctx) (a.instantiate_var lc)
| _ e := do state_t.lift $ trace e, pure "e_UNSUPPORTED"

meta def to_tf0.run {α} (t : to_tf0 α) : tactic α :=
prod.fst <$> state_t.run t {}

meta def tptpify_thf_ann (role : string) (n : string) (f : format) : format :=
format.group $ format.nest 1 $ "thf(" ++ format.group (
    n ++ "," ++ format.line ++ role ++ ",")
  ++ format.line ++ f ++ ")."

meta def to_tf0_file (cs : list (expr × expr)) (lems : list (expr × expr)) : to_tf0 (format × list (string × expr × expr)) := do
let sorts := _root_.consts_and_local_consts (cs.map prod.snd),
sort_decls ← sorts.mmap (λ c, do
  c' ← to_tf0.con_name c,
  pure $ tptpify_thf_ann "type" ("ty_" ++ c')
    (tptpify_binop ":" c' "$tType")),
-- state_t.lift $ trace (cs, lems),
ty_decls ← cs.mmap (λ ⟨c, t⟩, do
  t' ← to_tf0_ty t,
  c' ← to_tf0.con_name c,
  pure $ tptpify_thf_ann "type" ("ty_" ++ c') (tptpify_binop ":" c' t')),
lems ← state_t.lift $ lems.mfilter (λ ⟨pr, ty⟩, is_prop ty),
-- state_t.lift $ trace lems,
axs ← lems.mmap (λ ⟨pr, ty⟩, do
  n ← to_tf0.ax_name pr,
  ann ← tptpify_thf_ann "axiom" n <$> to_tf0_tm [] ty,
  pure (n, pr, ty, ann)),
let tptp := format.join $
  ((sort_decls ++ ty_decls ++ axs.map (λ ⟨n,pr,ty,ann⟩, ann)).map format.group)
  .intersperse (format.line ++ format.line),
pure (tptp, axs.map (λ ⟨n,pr,ty,ann⟩, (n, pr, ty)))

meta def get_head_const : expr → expr
| (app a b) := get_head_const a
| a@(lam _ _ _ b) := if b.has_var then a else get_head_const b
| e := e

meta def mk_monom_file (axs : list name) : tactic (format × list (string × expr × expr)) := do
goal ← retrieve (revert_all >> target),
let axs := goal.constants.filter is_good_const ++ axs,
axs ← close_under_references axs,
-- trace $ (axs.map name.to_string).qsort (λ a b, a < b),
repeat (intro1 >> skip),
(do tgt ← target, when (tgt ≠ `(false)) $
  mk_mapp ``classical.by_contradiction [some tgt] >>= eapply >> intro1 >> skip),
lems ← (++) <$> axs.mmap mk_const <*> local_context,
lems' ← monomorphize lems 2,
(cs'', lems'') ← intern_lems lems',
(to_tf0_file cs'' lems'').run

meta def filter_lemmas2 (axs : list name) : tactic (list (expr × expr)) := do
(tptp, ax_names) ← mk_monom_file axs,
-- trace tptp,
(tactic.unsafe_run_io $ do f ← io.mk_file_handle "hammer.p" io.mode.write, io.fs.write f tptp.to_string.to_char_buffer, io.fs.close f),
let ax_names := rb_map.of_list ax_names,
-- (failure : tactic unit),
tptp_out ← timetac "eprover-ho took" $ exec_cmd "bash" ["-c",
  "set -o pipefail; eprover-ho --cpu-limit=30 --proof-object=1 | " ++
    "grep -oP '(?<=file\\(..stdin.., ).*?(?=\\))'"]
  tptp.to_string,
let ns := tptp_out.split_on '\n',
pure $ do n ← ns, (ax_names.find n).to_list

meta def find_lemmas2 (max := 10) : tactic (list (expr × expr)) := do
axs ← timetac "Premise selection took" $ retrieve $
  revert_all >> target >>= select_for_goal,
let axs := (axs.take max).map (λ a, a.1),
-- trace "Premise selection:",
trace axs,
filter_lemmas2 axs

meta def reconstruct2 (axs : list (expr × expr)) : tactic unit :=
focus1 $ super.with_ground_mvars $ do
axs ← axs.mmap $ λ ⟨pr, ty⟩, super.clause.of_type_and_proof ty pr,
super.solve_with_goal {} axs

-- set_option pp.all true
example (x y : ℤ) (h : x ∣ y) (h2 : x ≤ y) (h3 : ¬ x + y < 0)
  (h4 : ∃ i : ℤ, i ≤ i + 1) : true := by do
ls ← local_context,
l1 ← mk_const ``add_comm,
l2 ← mk_const ``le_antisymm,
l3 ← mk_const ``exists_congr,
let ls : list expr := l1 :: l2 :: l3 :: ls,
-- ls ← (λ x, [x]) <$> get_local `h3,
ls' ← monomorphize ls 3,
ls'' ← intern_lems ls',
trace_state,
trace ls'',
-- ls''.mmap' (λ l'', (to_tf0_tm [] l''.2).run >>= trace),
(to_tf0_file ls''.1 ls''.2).run >>= trace,
triv

-- example (x y : ℤ) (h : x ∣ y) (h2 : x ≤ y) (h3 : ¬ x + y < 0) : true :=
-- by feature_search

end hammer

namespace tactic
namespace interactive
open interactive interactive.types lean.parser

meta def find_lemmas2 (axs : parse $ optional $ list_of ident) (max_lemmas := 100) : tactic unit := do
lems ←
  match axs with
  | none := hammer.find_lemmas2 max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "eprover-ho took" $
      hammer.filter_lemmas2 axs
  end,
trace "eprover-ho proof uses the following lemmas:",
lems.mmap' (λ ⟨l, t⟩, do
  l' ← pp l,
  -- t ← infer_type l >>= pp,
  t ← pp t,
  trace (format.nest 4 $ format.group $ "  " ++ l' ++ " :" ++ format.line ++ t)),
admit

meta def hammer2 (axs : parse $ optional $ list_of ident) (max_lemmas := 100) : tactic unit := do
lems ←
  match axs with
  | none := hammer.find_lemmas2 max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "eprover-ho took" $
      hammer.filter_lemmas2 axs
  end,
trace "eprover-ho proof uses the following lemmas:",
lems.mmap' (λ ⟨l, t⟩, do
  l' ← pp l,
  -- t ← infer_type l >>= pp,
  t ← pp t,
  trace (format.nest 4 $ format.group $ "  " ++ l' ++ " :" ++ format.line ++ t)),
hammer.reconstruct2 lems

end interactive
end tactic

-- set_option trace.super true
-- example (x y : ℤ) : x + y = y + x :=
-- by hammer2 [add_comm]
