import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma one_lt_sqrt2_mul_pi_div_three : (1 : ℝ) < Real.sqrt 2 * Real.pi / 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs2 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  nlinarith

