import tactic.hammer.monomorphization data.nat.gcd data.real.basic

example (x y : ℕ) : x ∣ x * y :=
by hammer2
