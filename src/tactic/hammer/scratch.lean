import tactic.hammer.fo_translation data.nat.gcd data.real.basic

set_option profiler true

example (x y : ℝ) (h : x < y) : ∃ z : ℚ, x < z ∧ (z : ℝ) < y :=
by find_lemmas_via_vampire
-- by feature_search
-- by find_lemmas_via_vampire [real.archimedean, exists_rat_btwn]

example (x y : ℝ) (h : x < y) : ∃ z : ℚ, x < z ∧ (z : ℝ) ≤ y :=
-- by feature_search 60
by find_lemmas_via_vampire 30

example {α} [linear_ordered_field α] [archimedean α] {x y : α} (h : x < y) :
  ∃ q : ℚ, x < q ∧ (q:α) < y :=
by find_lemmas_via_vampire

example (x y : ℕ ) : x > y ∨ x ≤ y :=
by find_lemmas_via_vampire

example {α} (x y z : list α) : x ++ (z ++ y) = (x ++ z) ++ y :=
by find_lemmas_via_vampire

example (x y : ℕ) : nat.gcd x y ∣ x :=
by find_lemmas_via_vampire

example (x y z : ℕ) : nat.gcd x y ∣ nat.gcd (x*z) y :=
by find_lemmas_via_vampire

example (x y : ℕ) : x ∣ x * y :=
by find_lemmas_via_vampire
-- by feature_search
-- by find_lemmas_via_vampire [dvd_mul_right]
-- by find_lemmas_via_vampire [dvd_mul_right, foo, foo'] -- [nat.gcd_dvd]

example (x y z : ℕ) : nat.gcd x y ∣ x * z :=
by find_lemmas_via_vampire
