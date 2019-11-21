import tactic.hammer.monomorphization data.nat.gcd data.real.basic

example (x y z : ℕ) : x.gcd y ∣ (x*z).gcd y :=
by hammer2
