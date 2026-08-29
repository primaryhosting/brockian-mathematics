import Mathlib

/-- The aliquot sum of `n`: the sum of its proper divisors. -/

def Semiperfect (n : ℕ) : Prop :=
  ∃ s ∈ n.properDivisors.powerset, ∑ d ∈ s, d = n

/-- A perfect number (aliquot sum equal to itself) is semiperfect: take the full
set of proper divisors as the witnessing subset.

The positivity hypothesis `hn` was requested in the statement but is not needed
for the proof. -/
