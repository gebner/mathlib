import tactic.hammer.monomorphization data.nat.gcd data.real.basic

-- bug
example {α} [linear_ordered_field α] [archimedean α] {x y : α} (h : x < y) :
  ∃ q : ℚ, x < q ∧ (q:α) < y :=
by hammer2
