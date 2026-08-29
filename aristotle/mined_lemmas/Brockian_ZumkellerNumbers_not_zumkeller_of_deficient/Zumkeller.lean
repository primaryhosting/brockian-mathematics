import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- A deficient number (one with `sigma n < 2 * n`) is never Zumkeller: a candidate subset
`S` of the divisors can neither contain `n` (then `2 * ∑ S ≥ 2 * n > sigma n`) nor omit it
(then `∑ S + n ≤ sigma n`, so `2 * ∑ S ≤ 2 * sigma n - 2 * n < sigma n`). -/
