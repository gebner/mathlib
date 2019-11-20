import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true

example {α} (x y z : list α) : x ++ (z ++ y) = (x ++ z) ++ y :=
by hammer2 30
