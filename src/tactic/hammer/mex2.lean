import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true

example (x y : ℝ) (h : x < y) : ∃ z : ℚ, x < z ∧ (z : ℝ) ≤ y :=
by hammer_via_monom 60
-- by feature_search
-- by find_lemmas_via_monom [real.archimedean, exists_rat_btwn]
