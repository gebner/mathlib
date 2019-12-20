import tactic.core super.utils data.equiv.basic data.vector

instance sort.inhabited : inhabited (Sort*) :=
⟨pempty⟩

instance int.inhabited' : inhabited ℤ := ⟨0⟩

open tactic

meta def tactic_state.fmt_expr (s : tactic_state) (e : expr) : format :=
match pp e s with
| result.success f _ := f
| result.exception _ _ _ := to_fmt e
end

meta def tactic.get_expr_formatter : tactic (expr → format) :=
tactic_state.fmt_expr <$> read

meta def expr.has_mvar (n : name) (e : expr) : tactic bool := do
ms ← e.sorted_mvars,
pure $ ms.existsb $ λ m, m.meta_uniq_name = n

open tactic

namespace hammer

@[derive decidable_eq]
meta inductive hol_ty
| tbool
| base (t : expr)
| arr (a b : hol_ty)

namespace hol_ty

meta instance : inhabited hol_ty := ⟨tbool⟩

meta def to_format (ef : expr → format) : hol_ty → format
| tbool := "o"
| (base t) := ((ef t).bracket "『" "』").group
| (arr a b) := (to_format a ++ format.space ++ "→" ++ format.line ++ to_format b).paren.group

meta instance : has_to_format hol_ty := ⟨to_format to_fmt⟩
meta instance : has_repr hol_ty := ⟨to_string ∘ to_fmt⟩
meta instance : has_to_string hol_ty := ⟨to_string ∘ to_fmt⟩
meta instance : has_to_tactic_format hol_ty := ⟨λ e, to_format <$> get_expr_formatter <*> pure e⟩

meta def of_expr : expr → hol_ty
| (expr.sort level.zero) := tbool
| t@(expr.pi n bi a b) :=
  if b.has_var then base t else
  arr (of_expr a) (of_expr b)
| t := base t

meta def map (f : expr → expr) : hol_ty → hol_ty
| tbool := tbool
| (base t) := base (f t)
| (arr a b) := arr a.map b.map

meta def all_expr (f : expr → bool) : hol_ty → bool
| tbool := tt
| (base t) := f t
| (arr a b) := all_expr a && all_expr b

meta def to_expr : hol_ty → expr
| tbool := `(Prop)
| (base t) := t
| (arr a b) := a.to_expr.imp b.to_expr

meta def sorts : hol_ty → list expr
| tbool := []
| (base t) := [t]
| (arr a b) := a.sorts ++ b.sorts

protected meta def lt : hol_ty → hol_ty → bool
| _ tbool := ff
| tbool _ := tt
| (base t) (base t') := t < t'
| (base t) _ := tt
| _ (base t) := ff
| (arr a b) (arr a' b') := lt a a' ∨ (a = a' ∧ lt b b')

meta instance : has_lt hol_ty := ⟨λ a b, a.lt b⟩

end hol_ty

@[derive decidable_eq]
meta inductive hol_lcon
| true | false
| neg | and | or | imp | iff
| eq (t : hol_ty)
| all (t : hol_ty) | ex (t : hol_ty)

namespace hol_lcon

meta instance : inhabited hol_lcon := ⟨true⟩

meta def to_format : hol_lcon → format
| true := "true"
| false := "false"
| neg := "¬"
| and := "∧"
| or := "∨"
| iff := "↔"
| imp := "→"
| (eq t) := "="
| (all t) := "∀"
| (ex t) := "∃"

meta instance : has_repr hol_lcon := ⟨to_string ∘ to_format⟩
meta instance : has_to_string hol_lcon := ⟨to_string ∘ to_format⟩
meta instance : has_to_format hol_lcon := ⟨to_format⟩
meta instance : has_to_tactic_format hol_lcon := ⟨pure ∘ to_format⟩

meta def to_expr : hol_lcon → tactic expr
| true := pure `(_root_.true)
| false := pure `(_root_.false)
| neg := pure `(_root_.not)
| and := pure `(_root_.and)
| or := pure `(_root_.or)
| iff := pure `(_root_.iff)
| imp := pure `(λ a b : Prop, a → b)
| (eq t) := do u ← infer_univ t.to_expr, pure $ (expr.const ``_root_.eq [u] : expr) t.to_expr
| (ex t) := do u ← infer_univ t.to_expr, pure $ (expr.const ``_root_.Exists [u] : expr) t.to_expr
| (all t) := pure (expr.lam `p binder_info.default (t.to_expr.imp `(Prop))
  (expr.pi `x binder_info.default t.to_expr ((expr.var 1).app (expr.var 0))))

open hol_ty
meta def ty : hol_lcon → hol_ty
| true := tbool
| false := tbool
| neg := tbool.arr tbool
| and := tbool.arr (tbool.arr tbool)
| or := tbool.arr (tbool.arr tbool)
| imp := tbool.arr (tbool.arr tbool)
| iff := tbool.arr (tbool.arr tbool)
| (eq t) := t.arr (t.arr tbool)
| (all t) := (t.arr tbool).arr tbool
| (ex t) := (t.arr tbool).arr tbool

meta def map (f : expr → expr) : hol_lcon → hol_lcon
| (all t) := all (t.map f)
| (ex t) := ex (t.map f)
| (eq t) := eq (t.map f)
| lc := lc

meta def all_expr (f : expr → bool) : hol_lcon → bool
| (all t) := t.all_expr f
| (ex t) := t.all_expr f
| (eq t) := t.all_expr f
| _ := tt

meta def sorts : hol_lcon → list expr
| (all t) := t.sorts
| (ex t) := t.sorts
| (eq t) := t.sorts
| _ := []

end hol_lcon

@[derive decidable_eq]
meta inductive hol_tm
| con (n : expr) (t : hol_ty)
| lcon (lc : hol_lcon)
| cast (t : hol_ty) (a : hol_tm)
| app (a b : hol_tm)
| lam (x : name) (t : hol_ty) (a : hol_tm)
| var (i : ℕ)

namespace hol_tm

meta instance : inhabited hol_tm := ⟨lcon hol_lcon.true⟩

meta def all (x : name) (t : hol_ty) (a : hol_tm) : hol_tm :=
app (lcon $ hol_lcon.all t) (lam x t a)

@[pattern] meta def imp (a b : hol_tm) : hol_tm :=
app (app (lcon $ hol_lcon.imp) a) b

@[pattern] meta def true : hol_tm :=
lcon hol_lcon.true

@[pattern] meta def false : hol_tm :=
lcon hol_lcon.false

meta def to_format_core (ef : expr → format) : hol_tm → list name → format
| (app (lcon (hol_lcon.all t)) (lam x _ a)) lctx :=
  ((to_fmt "∀ " ++ to_fmt x ++ " :" ++ format.line ++ t.to_format ef ++ ",").group ++
    format.line ++ to_format_core a (x::lctx)).paren.group
| (imp a b) lctx := (to_format_core a lctx ++ format.space ++ "→" ++ format.line ++ b.to_format_core lctx).paren.group
| (con n t) _ := ((ef n).bracket "「" "」").group
| (lcon lc) _ := to_fmt lc
| (cast t a) lctx := (to_format_core a lctx ++ format.space ++ ":" ++ format.line ++ t.to_format ef).paren.group
| (app a b) lctx := (to_format_core a lctx ++ format.line ++ to_format_core b lctx).paren.group
| (lam x t a) lctx :=
  ((to_fmt "λ " ++ to_fmt x ++ " :" ++ format.line ++ t.to_format ef ++ ",").group ++
    format.line ++ to_format_core a (x::lctx)).paren.group
| (var i) lctx :=
  match lctx.nth i with
  | (some n) := to_fmt n
  | _ := "#" ++ i
  end

meta def to_format (ef : expr → format) (t : hol_tm) : format :=
to_format_core ef t []

meta instance : has_repr hol_tm := ⟨to_string ∘ to_format to_fmt⟩
meta instance : has_to_string hol_tm := ⟨to_string ∘ to_format to_fmt⟩
meta instance : has_to_format hol_tm := ⟨to_format to_fmt⟩
meta instance : has_to_tactic_format hol_tm := ⟨λ e, to_format <$> get_expr_formatter <*> pure e⟩

meta def to_expr : hol_tm → tactic expr
| (con n t) := pure n
| (lcon lc) := lc.to_expr
| (app a b) := expr.app <$> a.to_expr <*> b.to_expr
| (cast t a) := a.to_expr
| (lam x t a) := expr.lam x binder_info.default t.to_expr <$> a.to_expr
| (var i) := pure (expr.var i)

meta def map (f : expr → expr) : hol_tm → hol_tm
| (con n t) := con (f n) (t.map f)
| (lcon lc) := lcon (lc.map f)
| (app a b) := app a.map b.map
| (cast t a) := cast (t.map f) a.map
| (lam x t a) := lam x (t.map f) a.map
| (var i) := var i

meta def all_expr (f : expr → bool) : hol_tm → bool
| (con n t) := f n && t.all_expr f
| (lcon lc) := lc.all_expr f
| (app a b) := a.all_expr && b.all_expr
| (cast t a) := t.all_expr f && a.all_expr
| (lam x t a) := t.all_expr f && a.all_expr
| (var i) := tt

meta def instantiate_expr_var (t : hol_tm) (e : expr) : hol_tm :=
t.map (λ f, f.instantiate_var e)

meta def abstract_local (t : hol_tm) (l : name) : hol_tm :=
t.map (λ f, f.abstract_local l)

meta def has_expr (t : hol_tm) (p : expr → bool) : bool :=
bnot $ t.all_expr $ λ e, bnot (p e)

meta def has_expr_var (t : hol_tm) : bool :=
t.has_expr expr.has_var

meta def has_expr_meta_var (t : hol_tm) : bool :=
t.has_expr expr.has_meta_var

meta def instantiate_mvars (t : hol_tm) : tactic hol_tm := do
s ← read,
pure $ t.map $ λ e,
  match tactic.instantiate_mvars e s with
  | result.success e _ := e
  | result.exception _ _ _ := e
  end

meta def lift_core (off : ℕ) : hol_tm → ℕ → hol_tm
| e@(con _ _) _ := e
| e@(lcon _) _ := e
| (var i) n := var (if i < n then i else i+off)
| (app a b) n := app (a.lift_core n) (b.lift_core n)
| (lam x t a) n := lam x t (a.lift_core (n+1))
| (cast t a) n := cast t (a.lift_core n)

meta def instantiate_var_core (z : hol_tm) : hol_tm → ℕ → hol_tm
| e@(con _ _) n := e
| e@(lcon _) n := e
| (app a b) n := app (a.instantiate_var_core n) (b.instantiate_var_core n)
| (lam x t a) n := lam x t (a.instantiate_var_core (n+1))
| (cast t a) n := cast t (a.instantiate_var_core n)
| (var i) n := if i = n then lift_core n z 0 else if i < n then var i else var (i-1)

meta def instantiate_var (t z : hol_tm) : hol_tm :=
instantiate_var_core z t 0

meta def has_var_idx : hol_tm → ℕ → bool
| (con _ _) n := ff
| (lcon _) n := ff
| (app a b) n := a.has_var_idx n || b.has_var_idx n
| (lam x t a) n := a.has_var_idx (n+1)
| (cast t a) n := a.has_var_idx n
| (var i) n := i = n

meta def has_var_core : hol_tm → ℕ → bool
| (con _ _) n := ff
| (lcon _) n := ff
| (app a b) n := a.has_var_core n || b.has_var_core n
| (lam x t a) n := a.has_var_core (n+1)
| (cast t a) n := a.has_var_core n
| (var i) n := i ≥ n

meta def has_var (t : hol_tm) : bool :=
t.has_var_core 0

meta def app' : hol_tm → hol_tm → hol_tm
| (lam x t a) b := a.instantiate_var b
| a b := app a b

meta def sorts : hol_tm → list expr
| (con n t) := t.sorts
| (lcon lc) := lc.sorts
| (app a b) := a.sorts ++ b.sorts
| (lam x t a) := t.sorts ++ a.sorts
| (cast t a) := t.sorts ++ a.sorts
| (var i) := []

meta def consts : hol_tm → list (expr × hol_ty)
| (con n t) := [(n, t)]
| (lcon lc) := []
| (app a b) := a.consts ++ b.consts
| (lam x t a) := a.consts
| (cast t a) := a.consts
| (var i) := []

meta def exprs (t : hol_tm) := t.sorts ++ t.consts.map prod.fst

meta def ty_core : hol_tm → list hol_ty → hol_ty
| (con _ t) _ := t
| (lcon lc) _ := lc.ty
| (app a b) lctx :=
  match a.ty_core lctx with
  | (hol_ty.arr _ ret_ty) := ret_ty
  | _ := hol_ty.base (expr.mk_sorry `(Type))
  end
| (cast t _) _ := t
| (lam x t a) lctx := t.arr (a.ty_core (t :: lctx))
| (var i) lctx := (lctx.nth i).get_or_else (hol_ty.base (expr.mk_sorry `(Type)))

meta def ty (t : hol_tm) : hol_ty :=
t.ty_core []

meta def get_app_fn : hol_tm → hol_tm
| (app a _) := get_app_fn a
| f := f

private meta def get_app_args_aux : list hol_tm → hol_tm → list hol_tm
| r (app f a) := get_app_args_aux (a::r) f
| r e         := r

meta def get_app_args : hol_tm → list hol_tm :=
get_app_args_aux []

meta def is_type (t : expr) : tactic bool := do
s ← infer_type t,
s ← whnf s,
pure $ match s with expr.sort _ := tt | _ := ff end

meta def mk_const (e : expr) : tactic hol_tm := do
t ← infer_type e,
pure $ con e (hol_ty.of_expr t)

meta def ensure_bool_core (lctx : list hol_ty) (e : hol_tm) : tactic hol_tm :=
let t := e.ty_core lctx in
if t = hol_ty.tbool then pure e else do
u ← whnf t.to_expr,
match u with
| (expr.sort u) := do
  pure $ app (con (expr.const ``_root_.nonempty [u]) (hol_ty.arr t hol_ty.tbool)) e
| _ := do
  e ← pp e,
  fail $ to_fmt "ensure_bool_core: not a type: " ++ e
end

meta def ensure_type (t : hol_ty) (e : hol_tm) (lctx : list hol_ty) : hol_tm :=
if e.ty_core lctx = t then e else cast t e

meta def safe_app (a b : hol_tm) (expected : hol_ty) (lctx : list hol_ty) : hol_tm :=
match a.ty_core lctx with
| (hol_ty.arr ta1 ta2) :=
  app a $ ensure_type ta1 b lctx
| _ := do
  app (cast (hol_ty.arr (b.ty_core lctx) expected) a) b
end

meta def of_expr_core : expr → list hol_ty → list name → tactic hol_tm
| (expr.app (expr.const ``eq _) t) lctx lctx_lean :=
  pure $ lcon $ hol_lcon.eq $ hol_ty.of_expr t
| e@(expr.app (expr.app (expr.const ``Exists _) t) p) lctx lctx_lean := do
  p' ← of_expr_core p lctx lctx_lean,
  let t' := hol_ty.of_expr t,
  pure $ app (lcon $ hol_lcon.ex t') $ ensure_type (t'.arr hol_ty.tbool) p' lctx
| `(%%x ∧ %%y) lctx lctx_lean := do
  x ← of_expr_core x lctx lctx_lean >>= ensure_bool_core lctx,
  y ← of_expr_core y lctx lctx_lean >>= ensure_bool_core lctx,
  pure $ app (app (lcon hol_lcon.and) x) y
| `(%%x ∨ %%y) lctx lctx_lean := do
  x ← of_expr_core x lctx lctx_lean >>= ensure_bool_core lctx,
  y ← of_expr_core y lctx lctx_lean >>= ensure_bool_core lctx,
  pure $ app (app (lcon hol_lcon.or) x) y
| `(%%x ↔ %%y) lctx lctx_lean := do
  x ← of_expr_core x lctx lctx_lean >>= ensure_bool_core lctx,
  y ← of_expr_core y lctx lctx_lean >>= ensure_bool_core lctx,
  pure $ app (app (lcon hol_lcon.iff) x) y
| `(¬ %%x) lctx lctx_lean := do
  x ← of_expr_core x lctx lctx_lean >>= ensure_bool_core lctx,
  pure $ app (lcon hol_lcon.neg) x
| `(_root_.false) lctx lctx_lean := pure false
| `(_root_.true) lctx lctx_lean := pure true
| e@(expr.pi n bi t a) lctx lctx_lean := do
  e_prop ← is_prop e,
  if ¬ e_prop then mk_const e else do
  if a.has_var then do
    let t' := hol_ty.of_expr t,
    ne' ← of_expr_core t lctx lctx_lean >>= ensure_bool_core lctx,
    l ← mk_local' n bi t,
    a ← of_expr_core (a.instantiate_var l) (t'::lctx) (l.local_uniq_name::lctx_lean),
    let a := a.abstract_local l.local_uniq_name,
    if a.has_expr_var then mk_const e else
    pure $ all n t' a
  else do
    t ← of_expr_core t lctx lctx_lean >>= ensure_bool_core lctx,
    a ← of_expr_core a lctx lctx_lean >>= ensure_bool_core lctx,
    pure $ imp t a
| e@(expr.app a b) lctx lctx_lean := do
  tb@(expr.pi _ bi dom cod) ← infer_type a >>= whnf |
    (do a ← pp a, fail $ to_fmt "of_expr_core (app _ _): does not have function type: " ++ a),
  if bi = binder_info.inst_implicit ∨ cod.has_var then
    mk_const e
  else do
    a' ← of_expr_core a lctx lctx_lean,
    b' ← of_expr_core b lctx lctx_lean,
    te ← infer_type e,
    pure $ safe_app a' b' (hol_ty.of_expr te) lctx
| e@(expr.lam n bi a b) lctx lctx_lean := do
  l ← mk_local' n bi a,
  let t' := hol_ty.of_expr a,
  b' ← of_expr_core (b.instantiate_var l) (t'::lctx) (l.local_uniq_name::lctx_lean),
  let b' := b'.abstract_local l.local_uniq_name,
  if b'.has_expr_var then
    mk_const e -- bailout
  else
    pure $ lam n t' b'
| l@(expr.local_const _ _ _ _) lctx lctx_lean :=
  match lctx_lean.index_of' l.local_uniq_name with
  | (some i) := pure $ var i
  | _ := mk_const l
  end
| m@(expr.mvar _ _ _) lctx lctx_lean :=
  match lctx_lean.index_of' m.meta_uniq_name with
  | (some i) := pure $ var i
  | _ := mk_const m
  end
| (expr.var i) _ _ := fail "of_expr_core (var _)"
| e lctx lctx_lean := mk_const e

meta def of_lemma_core_top : expr → list hol_ty → list name → tactic hol_tm
| (expr.pi n bi t e) lctx lctx_lean := do
  t' ← of_expr_core t lctx lctx_lean,
  ne' ← ensure_bool_core lctx t',
  is_nonempty ← option.is_some <$> try_core ((mk_app ``nonempty [t] >>= mk_instance) <|> mk_instance t),
  t_prop ← is_prop t,
  t_type ← is_type t,
  let e_has_var : bool := e.has_var,
  if t_prop ∨ ¬ e_has_var then do
    l ← mk_local' n bi t,
    let e := e.instantiate_var l,
    e' ← of_lemma_core_top e lctx lctx_lean,
    pure $ if is_nonempty then e' else imp ne' e'
  else do
    m ← mk_meta_var t,
    let e := e.instantiate_var m,
    let t'_ty := hol_ty.of_expr t,
    e' ← of_lemma_core_top e (t'_ty::lctx) (m.meta_uniq_name::lctx_lean),
    has_mvar ← e'.to_expr >>= expr.has_mvar m.meta_uniq_name,
    if has_mvar then do
      m' ← mk_const m,
      let e' := e'.instantiate_var m',
      pure $ if is_nonempty then e' else imp ne' e'
    else do
      let e' := all n t'_ty e',
      pure $ if is_nonempty then e' else imp ne' e'
| e lctx lctx_lean := do
  e' ← of_expr_core e lctx lctx_lean,
  ensure_bool_core lctx e'

meta def of_lemma (e : expr) : tactic hol_tm :=
of_lemma_core_top e [] []

open native

meta structure simplify_state :=
(do_canon : bool := tt)
(canon : rb_map expr expr := mk_rb_map)
(reprs : list expr := [])

@[reducible] meta def simpl := state_t simplify_state tactic

meta def canonize (e : expr) : simpl expr := do
⟨tt, canon, reprs⟩ ← get | pure e,
match canon.find e with
| some e' := pure e'
| none := do
  rs ← state_t.lift $ reprs.mfilter (λ r, option.is_some <$> try_core (is_def_eq r e)),
  match rs with
  | (r::_) := do
    modify $ λ st, { canon := st.canon.insert e r, ..st },
    pure r
  | [] := do
    modify $ λ st, { canon := st.canon.insert e e, reprs := e :: st.reprs, ..st },
    pure e
  end
end

meta def simplify_type : hol_ty → simpl hol_ty
| (hol_ty.arr a b) := hol_ty.arr <$> simplify_type a <*> simplify_type b
| (hol_ty.base b) :=
  if b = `(Prop) then pure hol_ty.tbool else do
  b ← canonize b,
  pure $ if b = `(Prop) then hol_ty.tbool else hol_ty.base b
| hol_ty.tbool := pure hol_ty.tbool

meta def replace_inst_by_true (e : hol_tm) (lctx : list hol_ty) : tactic hol_tm :=
if e.has_var ∨ e.ty_core lctx ≠ hol_ty.tbool then pure e else do
e' ← e.to_expr,
has_inst ← option.is_some <$> (try_core $ mk_instance e' <|>
  (do `(nonempty %%t) ← pure e', mk_instance t)),
pure $ if has_inst then true else e

meta def simplify : hol_tm → list hol_ty → simpl hol_tm
| (imp a b) lctx := do
  a ← simplify a lctx,
  match a with
  | true := simplify b lctx
  | _ := do
      a ← state_t.lift $ ensure_bool_core lctx a,
      b ← simplify b lctx,
      match b with
      | true := pure true
      | _ := pure $ imp a b
      end
  end
-- | e@(app (con (expr.const ``_root_.nonempty [l]) ty) t) lctx :=
--   if l = level.zero then simplify t lctx else do
--   let c : expr := expr.const ``_root_.nonempty [l],
--   t ← simplify t lctx,
--   t' ← state_t.lift t.to_expr,
--   has_inst ← option.is_some <$> state_t.lift (try_core $ mk_instance (c t') <|> mk_instance t'),
--   pure $ if has_inst then true else safe_app (con c ty) t hol_ty.tbool lctx
| e@(app a b) lctx := do
  e ← (λ a b, safe_app a b (e.ty_core lctx) lctx) <$> simplify a lctx <*> simplify b lctx,
  state_t.lift $ replace_inst_by_true e lctx
| (lam x t a) lctx := do
  t' ← simplify_type t,
  lam x t' <$> simplify a (t' :: lctx)
| (var i) lctx := pure $ var i
| lc@(lcon (hol_lcon.eq t)) lctx := (lcon ∘ hol_lcon.eq) <$> simplify_type t
| lc@(lcon (hol_lcon.all t)) lctx := (lcon ∘ hol_lcon.all) <$> simplify_type t
| lc@(lcon (hol_lcon.ex t)) lctx := (lcon ∘ hol_lcon.ex) <$> simplify_type t
| lc@(lcon _) lctx := pure lc
| (con n t) lctx := do
  e ← con <$> canonize n <*> simplify_type t,
  state_t.lift $ replace_inst_by_true e lctx
| (cast t a) lctx := simplify a lctx

#eval do t ← tactic.mk_const ``add_zero >>= infer_type, of_lemma t >>= trace
#eval do t ← tactic.mk_const ``vector.cons >>= infer_type, of_lemma t >>= trace
private def foo : ∀ f g : ℕ → ℕ, (∀ x, f x = g x) → f = g := @_root_.funext ℕ (λ _, ℕ)
#eval do t ← tactic.mk_const ``foo >>= infer_type, of_lemma t >>= trace
#eval do t ← tactic.mk_const ``equiv.equiv_congr >>= infer_type, of_lemma_core_top t [] [] >>= trace
#eval do t ← tactic.mk_const ``equiv.Pi_congr_right >>= infer_type, of_lemma_core_top t [] [] >>= trace

set_option pp.all true
#eval do t ← tactic.mk_const ``add_zero >>= infer_type, of_lemma_core_top t [] [] >>= trace ∘ list.dup_by_native id ∘ exprs

end hol_tm

end hammer
