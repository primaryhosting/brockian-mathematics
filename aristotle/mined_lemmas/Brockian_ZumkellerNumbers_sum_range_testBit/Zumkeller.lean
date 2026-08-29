import Mathlib

namespace Brockian.ZumkellerNumbers


def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- Any `x < 2 ^ k` is the sum of the powers of two given by its binary digits. -/
