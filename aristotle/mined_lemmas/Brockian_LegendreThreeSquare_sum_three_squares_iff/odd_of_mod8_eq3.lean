import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma odd_of_mod8_eq3 {n : ℕ} (hn : n % 8 = 3) : Odd n := by
  have : n % 2 = 1 := by omega
  exact Nat.odd_iff.2 this

