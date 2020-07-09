import tactic.hammer data.nat.gcd data.real.basic

example (x y : ℕ ) : x > y ∨ x ≤ y :=
by hammer4
