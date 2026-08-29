import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- No prime power is Zumkeller: prime powers are deficient, since
`sigma (p ^ k) = 1 + p + ⋯ + p ^ k < 2 * p ^ k`, while any Zumkeller number `m`
satisfies `2 * m ≤ sigma m` (the witnessing subset or its complement contains `m`). -/
