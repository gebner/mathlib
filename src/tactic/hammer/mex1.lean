import tactic.hammer data.nat.gcd data.real.basic

lemma exampl (x y : ℝ) (h : x < y) : ∃ z : ℚ, y > z ∧ x < z :=
-- by hammer3 20
by super [gt, exists_rat_btwn, *]

#print exampl
