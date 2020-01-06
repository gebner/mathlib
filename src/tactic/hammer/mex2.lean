import tactic.hammer data.nat.gcd data.real.basic

example (x y : ℝ) (h : x < y) : ∃ z : ℚ, x < z ∧ (z : ℝ) ≤ y :=
by hammer3 60 -- bug due to uninhabited (fintype ℚ)
-- by hammer2 [exists_rat_btwn, le_of_lt]
