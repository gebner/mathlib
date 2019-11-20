import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true
example (x y : ℕ) : x ∣ x * y :=
by hammer_via_monom
-- by feature_search
-- by find_lemmas_via_monom [dvd_mul_right]
-- by find_lemmas_via_monom [dvd_mul_right, foo, foo'] -- [nat.gcd_dvd]
