import tactic.hammer.monomorphization2 data.nat.gcd data.real.basic

example (x y : ℝ) (h : x < y) : ∃ z : ℚ, x < z ∧ (z : ℝ) < y :=
by hammer3 20
