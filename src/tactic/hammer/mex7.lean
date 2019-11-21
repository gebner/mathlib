import tactic.hammer.monomorphization data.nat.gcd data.real.basic

example (x y z : ℕ) : nat.gcd x y ∣ nat.gcd (x*z) y :=
by hammer2
