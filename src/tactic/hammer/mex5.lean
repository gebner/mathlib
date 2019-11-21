import tactic.hammer.monomorphization data.nat.gcd data.real.basic

example (x y z : list ℕ) : x ++ (z ++ y) = (x ++ z) ++ y :=
by hammer2 30
