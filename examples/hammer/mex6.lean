import tactic.hammer data.nat.gcd data.real.basic

set_option profiler true
example (x y : ℕ) : nat.gcd x y ∣ x :=
by hammer4
