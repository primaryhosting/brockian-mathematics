import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma zmod_isUnit_two_of_odd (n : ℕ) (hn : Odd n) : IsUnit (2 : ZMod n) := by
  exact (ZMod.isUnit_iff_coprime 2 n).2 (Nat.coprime_two_left.2 hn)

