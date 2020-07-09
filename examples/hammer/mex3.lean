import tactic.hammer data.nat.gcd data.real.basic

example {α} [linear_ordered_field α] [archimedean α] {x y : α} (h : x < y) :
  ∃ q : ℚ, x < q ∧ (q:α) < y :=
-- by hammer3 30
by hammer4
