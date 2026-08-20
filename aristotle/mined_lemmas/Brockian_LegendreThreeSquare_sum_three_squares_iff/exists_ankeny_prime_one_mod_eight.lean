import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_ankeny_prime_one_mod_eight (n : ℕ) (hn : n % 8 = 1) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  classical
  have hn_odd : Odd n := by
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have h2 : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  simpa using exists_prime_one_mod_four_and_eq_neg_inv n 2 hn_odd h2

/-- Variant of the Dirichlet/CRT prime choice for the *even* reduced residue classes.

For `n % 8 ∈ {2,6}`, write `n = 2*s` with `s` odd. We want an odd prime `q` such that
- `q ≡ -1 (mod s)` (so also `q ≡ -1 (mod n)`), and
- `q % 8` is a specific value (`1` or `5`) so that the Jacobi-symbol computation forces
  `J(-n | q) = 1`, hence `-n` is a square modulo `q`.

This lemma packages only the prime existence step: it does *not* compute Jacobi symbols. -/
