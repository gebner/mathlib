import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true

example (x y z : ℕ) : nat.gcd x y ∣ x * z :=
by hammer_via_monom
