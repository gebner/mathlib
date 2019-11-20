import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- set_option profiler true
set_option trace.super true

example {α} [linear_ordered_field α] [archimedean α] {x y : α} (h : x < y) :
  ∃ q : ℚ, x < q ∧ (q:α) < y :=
by hammer_via_monom
