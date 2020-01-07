import tactic.hammer data.nat.gcd data.real.basic

example (a b : ℕ) : a.lcm b * b.gcd a = a * b :=
by hammer3 [nat.gcd_mul_lcm, mul_comm, nat.gcd_comm, nat.lcm_comm]
