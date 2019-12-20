import tactic.core super.utils data.equiv.basic data.vector

universes u v

instance sort.inhabited : inhabited (Sort u) :=
⟨pempty⟩

instance int.inhabited' : inhabited ℤ := ⟨0⟩

open tactic

meta def tactic_state.pp {α} [has_to_tactic_format α] (s : tactic_state) (a : α) : format :=
match pp a s with
| result.success f _ := f
| result.exception (some msg) _ _ := msg ()
| result.exception _ _ _ := "<exception>"
end

meta def tactic.get_formatter {α} [has_to_tactic_format α] : tactic (α → format) :=
tactic_state.pp <$> read

meta def tactic_state.fmt_expr (s : tactic_state) (e : expr) : format := s.pp e

meta def tactic.get_expr_formatter : tactic (expr → format) := tactic.get_formatter

meta def expr.has_mvar (n : name) (e : expr) : tactic bool := do
ms ← e.sorted_mvars,
pure $ ms.existsb $ λ m, m.meta_uniq_name = n

open tactic

namespace hammer

@[derive decidable_eq]
inductive hol_ty (α : Type u) : Type u
| tbool {} : hol_ty
| base (t : α) : hol_ty
| arr (a b : hol_ty) : hol_ty

@[reducible] meta def ehol_ty := hol_ty expr

namespace hol_ty

variables {α : Type u} {β : Type v}

instance : inhabited (hol_ty α) := ⟨tbool⟩

meta def to_format (ef : α → format) : hol_ty α → format
| tbool := "o"
| (base t) := ((ef t).bracket "『" "』").group
| (arr a b) := (to_format a ++ format.space ++ "→" ++ format.line ++ to_format b).paren.group

meta instance [has_to_format α] : has_to_format (hol_ty α) := ⟨to_format to_fmt⟩
meta instance [has_to_format α] : has_repr (hol_ty α) := ⟨to_string ∘ to_fmt⟩
meta instance [has_to_format α] : has_to_string (hol_ty α) := ⟨to_string ∘ to_fmt⟩
meta instance {α : Type} [has_to_tactic_format α] : has_to_tactic_format (hol_ty α) :=
⟨λ e, to_format <$> get_formatter <*> pure e⟩

meta def of_expr : expr → hol_ty expr
| (expr.sort level.zero) := tbool
| t@(expr.pi n bi a b) :=
  if b.has_var then base t else
  arr (of_expr a) (of_expr b)
| t := base t

def map (f : α → β) : hol_ty α → hol_ty β
| tbool := tbool
| (base t) := base (f t)
| (arr a b) := arr a.map b.map

def all_expr (f : α → bool) : hol_ty α → bool
| tbool := tt
| (base t) := f t
| (arr a b) := all_expr a && all_expr b

meta def to_expr : hol_ty expr → expr
| tbool := `(Prop)
| (base t) := t
| (arr a b) := a.to_expr.imp b.to_expr

def sorts : hol_ty α → list α
| tbool := []
| (base t) := [t]
| (arr a b) := a.sorts ++ b.sorts

protected def lt [has_lt α] [decidable_rel ((<) : α → α → Prop)] [_root_.decidable_eq α]
  : hol_ty α → hol_ty α → bool
| _ tbool := ff
| tbool _ := tt
| (base t) (base t') := t < t'
| (base t) _ := tt
| _ (base t) := ff
| (arr a b) (arr a' b') := lt a a' ∨ (a = a' ∧ lt b b')

meta instance  [has_lt α] [decidable_rel ((<) : α → α → Prop)] [_root_.decidable_eq α] :
  has_lt (hol_ty α) :=
⟨λ a b, a.lt b⟩

end hol_ty

@[derive decidable_eq]
inductive hol_lcon (α : Type u) : Type u
| true {}: hol_lcon
| false {} : hol_lcon
| neg {} : hol_lcon
| and {} : hol_lcon
| or {} : hol_lcon
| imp {} : hol_lcon
| iff {} : hol_lcon
| eq (t : hol_ty α) : hol_lcon
| all (t : hol_ty α) : hol_lcon
| ex (t : hol_ty α) : hol_lcon

namespace hol_lcon
variables {α : Type u} {β : Type v}

instance : inhabited (hol_lcon α) := ⟨true⟩

def to_string : hol_lcon α → string
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

meta instance : has_repr (hol_lcon α) := ⟨to_string⟩
meta instance : has_to_string (hol_lcon α) := ⟨to_string⟩
meta instance : has_to_format (hol_lcon α) := ⟨to_fmt ∘ to_string⟩
meta instance : has_to_tactic_format (hol_lcon α) := ⟨λ lc, pure lc.to_string⟩

meta def to_expr : hol_lcon expr → tactic expr
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
def ty : hol_lcon α → hol_ty α
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

def map (f : α → β) : hol_lcon α → hol_lcon β
| (all t) := all (t.map f)
| (ex t) := ex (t.map f)
| (eq t) := eq (t.map f)
| true := true
| false := false
| neg := neg
| and := and
| or := or
| imp := imp
| iff := iff

def all_expr (f : α → bool) : hol_lcon α → bool
| (all t) := t.all_expr f
| (ex t) := t.all_expr f
| (eq t) := t.all_expr f
| _ := tt

def sorts : hol_lcon α → list α
| (all t) := t.sorts
| (ex t) := t.sorts
| (eq t) := t.sorts
| _ := []

end hol_lcon

inductive hol_tm (α : Type u) (β : Type v) : Type (max u v)
| con (n : β) (t : hol_ty α) : hol_tm
| lcon {} (lc : hol_lcon α) : hol_tm
| cast (t : hol_ty α) (a : hol_tm) : hol_tm
| app (a b : hol_tm) : hol_tm
| lam (x : name) (t : hol_ty α) (a : hol_tm) : hol_tm
| var {} (i : ℕ) : hol_tm

@[reducible] meta def ehol_tm := hol_tm expr expr

namespace hol_tm
variables {α : Type u} {β : Type v}

meta instance [decidable_eq α] [decidable_eq β] : decidable_eq (hol_tm α β) :=
by mk_dec_eq_instance

instance : inhabited (hol_tm α β) := ⟨lcon hol_lcon.true⟩

def all (x : name) (t : hol_ty α) (a : hol_tm α β) : hol_tm α β :=
app (lcon $ hol_lcon.all t) (lam x t a)

@[pattern] def imp (a b : hol_tm α β) : hol_tm α β :=
app (app (lcon $ hol_lcon.imp) a) b

@[pattern] def true : hol_tm α β :=
lcon hol_lcon.true

@[pattern] def false : hol_tm α β :=
lcon hol_lcon.false

section
variables [has_to_format α] [has_to_format β]

meta def to_format_core : hol_tm α β → list name → format
| (app (lcon (hol_lcon.all t)) (lam x _ a)) lctx :=
  ((to_fmt "∀ " ++ to_fmt x ++ " :" ++ format.line ++ to_fmt t ++ ",").group ++
    format.line ++ to_format_core a (x::lctx)).paren.group
| (imp a b) lctx := (to_format_core a lctx ++ format.space ++ "→" ++ format.line ++ b.to_format_core lctx).paren.group
| (con n t) _ := ((to_fmt n).bracket "「" "」").group
| (lcon lc) _ := to_fmt lc
| (cast t a) lctx := (to_format_core a lctx ++ format.space ++ ":" ++ format.line ++ to_fmt t).paren.group
| (app a b) lctx := (to_format_core a lctx ++ format.line ++ to_format_core b lctx).paren.group
| (lam x t a) lctx :=
  ((to_fmt "λ " ++ to_fmt x ++ " :" ++ format.line ++ to_fmt t ++ ",").group ++
    format.line ++ to_format_core a (x::lctx)).paren.group
| (var i) lctx :=
  match lctx.nth i with
  | (some n) := to_fmt n
  | _ := "#" ++ i
  end

meta def to_format (t : hol_tm α β) : format :=
to_format_core t []

meta instance : has_to_format (hol_tm α β) := ⟨to_format⟩
meta instance : has_repr (hol_tm α β) := ⟨to_string ∘ to_fmt⟩
meta instance : has_to_string (hol_tm α β) := ⟨to_string ∘ to_fmt⟩

end

meta instance {α} {β} [has_to_tactic_format α] [has_to_tactic_format β] : has_to_tactic_format (hol_tm α β) :=
⟨λ e, do f ← get_formatter, g ← get_formatter, pure $ @to_format _ _ ⟨f⟩ ⟨g⟩ e⟩

meta def to_expr : ehol_tm → tactic expr
| (con n t) := pure n
| (lcon lc) := lc.to_expr
| (app a b) := expr.app <$> a.to_expr <*> b.to_expr
| (cast t a) := a.to_expr
| (lam x t a) := expr.lam x binder_info.default t.to_expr <$> a.to_expr
| (var i) := pure (expr.var i)

def map {α' β'} (f : α → α') (g : β → β') : hol_tm α β → hol_tm α' β'
| (con n t) := con (g n) (t.map f)
| (lcon lc) := lcon (lc.map f)
| (app a b) := app a.map b.map
| (cast t a) := cast (t.map f) a.map
| (lam x t a) := lam x (t.map f) a.map
| (var i) := var i

def map' (f : α → β) : hol_tm α α → hol_tm β β :=
map f f

def all_expr (f : α → bool) (g : β → bool) : hol_tm α β → bool
| (con n t) := g n && t.all_expr f
| (lcon lc) := lc.all_expr f
| (app a b) := a.all_expr && b.all_expr
| (cast t a) := t.all_expr f && a.all_expr
| (lam x t a) := t.all_expr f && a.all_expr
| (var i) := tt

def all_expr' (f : α → bool) : hol_tm α α → bool :=
all_expr f f

meta def instantiate_expr_var (t : ehol_tm) (e : expr) : ehol_tm :=
t.map' (λ f, f.instantiate_var e)

meta def abstract_local (t : hol_tm expr expr) (l : name) : hol_tm _ _ :=
t.map' (λ f, f.abstract_local l)

meta def has_expr (t : hol_tm expr expr) (p : expr → bool) : bool :=
bnot $ t.all_expr' $ λ e, bnot (p e)

meta def has_expr_var (t : hol_tm expr expr) : bool :=
t.has_expr expr.has_var

meta def has_expr_meta_var (t : hol_tm expr expr) : bool :=
t.has_expr expr.has_meta_var

meta def instantiate_mvars (t : hol_tm expr expr) : tactic ehol_tm := do
s ← read,
pure $ t.map' $ λ e,
  match tactic.instantiate_mvars e s with
  | result.success e _ := e
  | result.exception _ _ _ := e
  end

def lift_core (off : ℕ) : hol_tm α β → ℕ → hol_tm α β
| e@(con _ _) _ := e
| e@(lcon _) _ := e
| (var i) n := var (if i < n then i else i+off)
| (app a b) n := app (a.lift_core n) (b.lift_core n)
| (lam x t a) n := lam x t (a.lift_core (n+1))
| (cast t a) n := cast t (a.lift_core n)

def instantiate_var_core (z : hol_tm α β) : hol_tm α β → ℕ → hol_tm α β
| e@(con _ _) n := e
| e@(lcon _) n := e
| (app a b) n := app (a.instantiate_var_core n) (b.instantiate_var_core n)
| (lam x t a) n := lam x t (a.instantiate_var_core (n+1))
| (cast t a) n := cast t (a.instantiate_var_core n)
| (var i) n := if i = n then lift_core n z 0 else if i < n then var i else var (i-1)

def instantiate_var (t z : hol_tm α β) : hol_tm α β :=
instantiate_var_core z t 0

def has_var_idx : hol_tm α β → ℕ → bool
| (con _ _) n := ff
| (lcon _) n := ff
| (app a b) n := a.has_var_idx n || b.has_var_idx n
| (lam x t a) n := a.has_var_idx (n+1)
| (cast t a) n := a.has_var_idx n
| (var i) n := i = n

def has_var_core : hol_tm α β → ℕ → bool
| (con _ _) n := ff
| (lcon _) n := ff
| (app a b) n := a.has_var_core n || b.has_var_core n
| (lam x t a) n := a.has_var_core (n+1)
| (cast t a) n := a.has_var_core n
| (var i) n := i ≥ n

def has_var (t : hol_tm α β) : bool :=
t.has_var_core 0

def app' : hol_tm α β → hol_tm α β → hol_tm α β
| (lam x t a) b := a.instantiate_var b
| a b := app a b

def sorts : hol_tm α β → list α
| (con n t) := t.sorts
| (lcon lc) := lc.sorts
| (app a b) := a.sorts ++ b.sorts
| (lam x t a) := t.sorts ++ a.sorts
| (cast t a) := t.sorts ++ a.sorts
| (var i) := []

def consts : hol_tm α β → list (β × hol_ty α)
| (con n t) := [(n, t)]
| (lcon lc) := []
| (app a b) := a.consts ++ b.consts
| (lam x t a) := a.consts
| (cast t a) := a.consts
| (var i) := []

def exprs (t : hol_tm α α) := t.sorts ++ t.consts.map prod.fst

def ty_core : hol_tm α β → list (hol_ty α) → hol_ty α
| (con _ t) _ := t
| (lcon lc) _ := lc.ty
| (app a b) lctx :=
  match a.ty_core lctx with
  | (hol_ty.arr _ ret_ty) := ret_ty
  | _ := default _
  end
| (cast t _) _ := t
| (lam x t a) lctx := t.arr (a.ty_core (t :: lctx))
| (var i) lctx := (lctx.nth i).get_or_else (default _)

def ty (t : hol_tm α β) : hol_ty α :=
t.ty_core []

def get_app_fn : hol_tm α β → hol_tm α β
| (app a _) := get_app_fn a
| f := f

private def get_app_args_aux : list (hol_tm α β) → hol_tm α β → list (hol_tm α β)
| r (app f a) := get_app_args_aux (a::r) f
| r e         := r

def get_app_args : hol_tm α β → list (hol_tm α β) :=
get_app_args_aux []

meta def is_type (t : expr) : tactic bool := do
s ← infer_type t,
s ← whnf s,
pure $ match s with expr.sort _ := tt | _ := ff end

meta def mk_const (e : expr) : tactic ehol_tm := do
t ← infer_type e,
pure $ con e (hol_ty.of_expr t)

meta def ensure_bool_core (lctx : list (hol_ty expr)) (e : ehol_tm) : tactic ehol_tm :=
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

meta def ensure_type (t : hol_ty expr) (e : ehol_tm) (lctx : list (hol_ty expr)) : ehol_tm :=
if e.ty_core lctx = t then e else cast t e

meta def safe_app (a b : ehol_tm) (expected : hol_ty expr) (lctx : list (hol_ty expr)) : ehol_tm :=
match a.ty_core lctx with
| (hol_ty.arr ta1 ta2) :=
  app a $ ensure_type ta1 b lctx
| _ := do
  app (cast (hol_ty.arr (b.ty_core lctx) expected) a) b
end

meta def of_expr_core : expr → list (hol_ty expr) → list name → tactic ehol_tm
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

meta def of_lemma_core_top : expr → list (hol_ty expr) → list name → tactic ehol_tm
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

meta def of_lemma (e : expr) : tactic ehol_tm :=
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

meta def simplify_type : hol_ty expr → simpl (hol_ty expr)
| (hol_ty.arr a b) := hol_ty.arr <$> simplify_type a <*> simplify_type b
| (hol_ty.base b) :=
  if b = `(Prop) then pure hol_ty.tbool else do
  b ← canonize b,
  pure $ if b = `(Prop) then hol_ty.tbool else hol_ty.base b
| hol_ty.tbool := pure hol_ty.tbool

meta def replace_inst_by_true (e : ehol_tm) (lctx : list (hol_ty expr)) : tactic ehol_tm :=
if e.has_var ∨ e.ty_core lctx ≠ hol_ty.tbool then pure e else do
e' ← e.to_expr,
has_inst ← option.is_some <$> (try_core $ mk_instance e' <|>
  (do `(nonempty %%t) ← pure e', mk_instance t)),
pure $ if has_inst then true else e

meta def simplify : hol_tm expr expr → list (hol_ty expr) → simpl ehol_tm
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
