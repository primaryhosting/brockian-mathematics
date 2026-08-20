import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma one_lt_pi_div_three : (1 : ℝ) < Real.pi / 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- divide by 3>0
  have h3 : (0 : ℝ) < 3 := by norm_num
  have : (3 : ℝ) / 3 < Real.pi / 3 := (div_lt_div_of_pos_right hpi h3)
  simpa using this

