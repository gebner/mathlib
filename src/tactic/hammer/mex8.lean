import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true
example (x y : ℕ) : x ∣ x * y :=
by hammer2
-- by feature_search
-- by find_lemmas2 [dvd_mul_right]
-- by find_lemmas2 [dvd_mul_right, foo, foo'] -- [nat.gcd_dvd]
