import tactic.core

universes u

class is_associative' {α : Sort u} (op : α → α → α) :=
(assoc : ∀ a b c, op (op a b) c = op a (op b c))

instance is_associative'.of_is_associative {α} (op) [is_associative α op] : is_associative' op :=
⟨is_associative.assoc _⟩

class is_commutative' {α : Sort u} (op : α → α → α) :=
(comm : ∀ a b, op a b = op b a)

instance is_commutative'.of_is_commutative {α} (op) [is_commutative α op] : is_commutative' op :=
⟨is_commutative.comm _⟩

instance and.is_associative' : is_associative' (∧) := ⟨by intros a b c; rw and_assoc⟩
instance or.is_associative' : is_associative' (∨) := ⟨by intros a b c; rw or_assoc⟩
instance and.is_commutative' : is_commutative' (∧) := ⟨by intros a b; rw and_comm⟩
instance or.is_commutative' : is_commutative' (∨) := ⟨by intros a b; rw or_comm⟩

def set_builder (α : Type) := list α → list α

namespace set_builder

instance {α} : has_emptyc (set_builder α) := ⟨id⟩

instance {α} [decidable_eq α] : has_insert α (set_builder α) :=
⟨λ x b s, if x ∈ s then s else x :: s⟩

instance {α} : has_union (set_builder α) := ⟨(∘)⟩

def to_list {α} (b : set_builder α) : list α := b []

end set_builder

namespace acsimp

open tactic expr

meta def con (n : name) (l : list level := []) : expr :=
const n l

section
variables (acmatch : expr → expr → tactic expr)

meta def commit_to_this_branch := @try_core

meta def orelse_option {α} (t : tactic (option α)) (s : tactic α) : tactic α :=
do a ← try_core t,
match a with
| some (some a) := pure a
| some none := fail "orelse_option"
| none := s
end

local infixr `<|>'`:2 := orelse_option

lemma congr_arg2 {α} (f : α → α → α) {a a' b b' : α} :
  a = a' → b = b' → f a b = f a' b' :=
by intros; cc

meta def accongr (op is_assoc : expr) (is_comm : option expr) :
  ∀ lhs rhs lhs' rhs' : expr, tactic expr | lhs rhs lhs' rhs' :=
do
--  trace (con ``accongr [] op is_assoc lhs rhs lhs' rhs'),
(do app (app op' a) b ← pure rhs, is_def_eq op op',
    commit_to_this_branch $
    (do prf ← accongr lhs a lhs' (op b rhs'),
        -- prf : lhs + lhs' = a + (b + rhs')
        mk_eq_symm (is_assoc a b rhs') >>= mk_eq_trans prf) <|>
    (do some is_comm_prf ← pure is_comm,
        prf ← accongr lhs b lhs' (op a rhs'),
        -- prf : lhs + lhs' = b + (a + rhs')
        prfrhs'rfl ← mk_eq_refl rhs',
        prfcongr ← mk_mapp ``congr_arg2 [none, op, none, none, none, none, is_comm_prf b a, prfrhs'rfl],
        prfassoc ← mk_eq_symm (is_assoc b a rhs'),
        mk_eq_trans prfassoc prfcongr >>= mk_eq_trans prf)
    -- wanted : lhs + lhs' = (a + b) + rhs'
) <|>'
(do prf ← acmatch lhs rhs,
    prf' ← acmatch lhs' rhs',
    mk_mapp ``congr_arg2 [none, op, none, none, none, none, prf, prf'])

meta def try_subsingleton (lhs rhs : expr) : tactic expr :=
mk_app ``subsingleton.elim [lhs, rhs]

-- #eval try_subsingleton `(()) `(()) >>= infer_type >>= trace

meta def try_rfl (lhs rhs : expr) : tactic expr :=
is_def_eq lhs rhs >> mk_eq_refl rhs

meta def is_assoc_app : expr → tactic (expr × expr)
| (app (app f a) b) := do
  prf ← mk_mapp ``is_associative'.assoc [none, f, none],
  pure (f, prf)
| _ := fail "is_assoc_app"

meta def is_comm_op (op : expr) : tactic (option expr) :=
try_core $ mk_mapp ``is_commutative'.comm [none, op, none]

meta def try_reassoc_left : expr → expr → tactic (option expr)
| lhs@(app (app f (app (app f' a) b)) c) rhs := do
  is_def_eq f f',
  (op, is_assoc) ← is_assoc_app lhs,
  commit_to_this_branch $ do
  prf ← acmatch (f a (f b c)) rhs,
  mk_eq_trans (is_assoc a b c) prf
| _ _ := fail "try_reassoc_left"

meta def try_accongr : expr → expr → tactic (option expr)
| lhs@(app (app f a) b) rhs@(app (app f' c) d) := do
  is_def_eq f f',
  (op, is_assoc) ← is_assoc_app lhs,
  is_comm ← is_comm_op op,
  commit_to_this_branch $
  accongr acmatch op is_assoc is_comm a c b d <|>
  (do some is_comm_prf ← pure is_comm,
      prf ← accongr acmatch op is_assoc is_comm a d b c,
      -- prf : a + b = d + c
      mk_eq_trans prf (is_comm_prf d c))
  -- wanted : a + b = c + d
| _ _ := fail "try_accongr"

meta def try_assign : expr → expr → tactic expr
| lhs@(mvar _ _ _) rhs := do
  -- trace (con ``try_assign [] lhs rhs),
  unify lhs rhs,
  mk_eq_refl rhs
| _ _ := fail "try_assign"

meta def try_congr (lhs rhs : expr) : tactic expr := do
app fl al ← pure lhs,
app fr ar ← pure rhs,
tfl ← infer_type fl,
tfr ← infer_type fr,
is_def_eq tfl tfr,
fprf ← acmatch fl fr,
aprf ← acmatch al ar,
to_expr ``(_root_.congr %%fprf %%aprf)

meta def unify_op : expr → expr → tactic unit
| (app (app f _) _) (app (app g _) _) := unify f g
| _ _ := failure

meta def acmatch_core (lhs rhs : expr) : tactic expr := do
lhs ← instantiate_mvars lhs,
try (unify_op lhs rhs),
try_assign lhs rhs <|>
try_subsingleton lhs rhs <|>
try_rfl lhs rhs <|>
try_reassoc_left acmatch lhs rhs <|>'
try_accongr acmatch lhs rhs <|>'
try_congr acmatch lhs rhs

end

meta def acmatch : expr → expr → tactic expr | lhs rhs := do
-- trace (con `acmatch [] lhs rhs),
acmatch_core acmatch lhs rhs --<|> (trace ((const `acmatch_failed [] : expr) lhs rhs) >> failure)

end acsimp
