import tactic.hammer.monomorphization data.nat.gcd data.real.basic

example (a b : ℕ) : a.gcd b * b.lcm a = a * b :=
by hammer2 [nat.gcd_mul_lcm, mul_comm, nat.gcd_comm, nat.lcm_comm]
