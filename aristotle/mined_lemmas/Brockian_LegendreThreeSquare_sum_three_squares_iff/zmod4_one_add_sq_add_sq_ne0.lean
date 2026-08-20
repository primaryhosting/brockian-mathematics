import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma zmod4_one_add_sq_add_sq_ne0 : ∀ y z : ZMod 4, (1 + y ^ 2 + z ^ 2) ≠ 0 := by
  decide

