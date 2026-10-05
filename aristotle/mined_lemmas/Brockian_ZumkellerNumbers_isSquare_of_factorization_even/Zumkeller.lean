import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset


def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- If every prime exponent in the factorization of `t` is even, then `t` is a square. -/
