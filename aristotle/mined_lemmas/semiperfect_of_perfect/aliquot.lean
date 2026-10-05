import Mathlib

/-- The aliquot sum of `n`: the sum of its proper divisors. -/

def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `n` is semiperfect if some set of proper divisors of `n` sums to `n`. -/
