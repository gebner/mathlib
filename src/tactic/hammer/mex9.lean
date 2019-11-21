import tactic.hammer.monomorphization data.nat.gcd data.real.basic

example (x y z : ℕ) : nat.gcd x y ∣ z * x :=
by hammer2
