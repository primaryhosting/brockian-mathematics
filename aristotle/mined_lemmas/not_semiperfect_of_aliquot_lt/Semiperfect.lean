import Mathlib


def Semiperfect (n : ℕ) : Prop :=
  ∃ s ∈ n.properDivisors.powerset, ∑ d ∈ s, d = n

/-- If the aliquot sum of `n` is less than `n` (i.e. `n` is deficient), then no subset of
the proper divisors of `n` can sum to `n`, so `n` is not semiperfect. -/
