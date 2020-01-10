import tactic.hammer data.nat.gcd data.real.basic

set_option trace.super true
example (x y z : ℕ) : nat.gcd x y ∣ z * x :=
by hammer3 30
