import tactic.hammer.monomorphization2 data.nat.gcd data.real.basic

example (x y z : ℕ) : x.gcd y ∣ (x*z).gcd (0+y) :=
by hammer3 50
