import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_ankeny_prime (n : ℕ) (hn : n % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  classical
  have hn_odd : Odd n := GeometryOfNumbers.NumberTheory.odd_of_mod8_eq3 hn
  have h2 : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  simpa using exists_prime_one_mod_four_and_eq_neg_inv n 2 hn_odd h2

