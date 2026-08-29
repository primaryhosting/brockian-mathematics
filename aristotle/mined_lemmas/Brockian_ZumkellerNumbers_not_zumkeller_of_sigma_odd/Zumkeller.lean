import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is Zumkeller if its divisors can be split so that one part sums to half
the total divisor sum. -/

def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- If the sum of divisors of `n` is odd, then `n` is not Zumkeller. -/
