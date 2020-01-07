import tactic.hammer data.nat.gcd data.real.basic

example (x y : ℕ) : x ∣ x * y :=
by hammer3
