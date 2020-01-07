import tactic.hammer data.nat.gcd data.real.basic

example (x y z : list ℕ) : x ++ (z ++ y) = (x ++ z) ++ y :=
by hammer3 30
