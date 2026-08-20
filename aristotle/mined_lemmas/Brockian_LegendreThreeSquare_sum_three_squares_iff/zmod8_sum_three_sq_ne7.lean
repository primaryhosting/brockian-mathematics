import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma zmod8_sum_three_sq_ne7 : ∀ x y z : ZMod 8, (x ^ 2 + y ^ 2 + z ^ 2) ≠ 7 := by
  decide

