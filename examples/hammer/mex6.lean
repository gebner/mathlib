import tactic.hammer data.nat.gcd data.real.basic

example (x y : ℕ) : nat.gcd x y ∣ x :=
by hammer4
