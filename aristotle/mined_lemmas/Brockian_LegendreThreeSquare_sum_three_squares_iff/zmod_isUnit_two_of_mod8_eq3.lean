import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma zmod_isUnit_two_of_mod8_eq3 (n : ℕ) (hn : n % 8 = 3) : IsUnit (2 : ZMod n) :=
  zmod_isUnit_two_of_odd n (odd_of_mod8_eq3 hn)

