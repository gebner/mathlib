import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true

example (x y : ℕ) : nat.gcd x y ∣ x :=
by hammer_via_monom 10
