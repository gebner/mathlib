import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true

example (x y : ℕ ) : x > y ∨ x ≤ y :=
by hammer2
