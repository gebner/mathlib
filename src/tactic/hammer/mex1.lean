import tactic.hammer data.nat.gcd data.real.basic

example (x y : ℝ) (h : x < y) : ∃ z : ℚ, y > z ∧ x < z :=
by hammer3 20
