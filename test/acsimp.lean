import tactic.acsimp data.rat

open acsimp tactic expr native

example (y z : ℤ) : true := by do
x ← mk_meta_var `(ℤ),
w ← mk_meta_var `(ℤ),
y ← get_local `y,
z ← get_local `z,
t ← to_expr ``((-%%x) + %%x + %%w),
let s := `(%%z + %%y + (-(%%y : ℤ)) : ℤ),
acmatch t s >>= trace,
triv

@[irreducible] def foo : Prop := false
@[irreducible] def bar : Prop := false

#eval acsimp.simp_lemmas.mk_default simp_lemmas.empty >>= trace

#eval do
l ← mk_const ``and_not_self,
let sls := rb_map.of_list [(``and, [l])],
lhs ← to_expr ``(foo ∧ bar ∧ ¬ foo),
acsimp_core sls lhs >>= trace

-- set_option profiler true

example (a b : Prop) : (a ∧ b ∧ ¬ a) = false :=
by acsimp only [and_not_self, false_and]

example (a b : Prop) : ((a ∨ ¬ b) ∨ (b ∨ ¬ a)) = true :=
by acsimp only [classical.em, true_or]

example (a b c : ℤ) : a + b + (-a) + b = b + b :=
by acsimp only [neg_add_self, zero_add]

example (a b c : ℤ) : (a + b) * (a - b) = a*a - b*b :=
by acsimp only [right_distrib,
  neg_add_self, zero_add,
  eq_self_iff_true, sub_eq_add_neg,
  (neg_mul_eq_mul_neg _ _).symm]

example (a b : ℚ) (h : a ≠ 0) (c : ℚ) (h2 : b * b = c) :
  b * a * b * a⁻¹ = c :=
begin
  acsimp only [mul_inv_cancel h, one_mul],
  guard_target b * b = c,
  exact h2
end
