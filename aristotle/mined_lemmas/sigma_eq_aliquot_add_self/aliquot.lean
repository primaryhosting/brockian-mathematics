import Mathlib

/-- The aliquot sum of `n`: the sum of the proper divisors of `n`. -/

def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- The sum of all divisors of `n` equals its aliquot sum plus `n` itself.
The positivity hypothesis `hn` was requested in the statement but is not needed
for the proof (for `n = 0` both sides are `0`). -/
