import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma volume_ankenyEllipsoidL2_gt (n q : ℝ) (hn : 0 < n) (hq : 0 < q) :
    ENNReal.ofReal (16 * (n * q)) < volume (ankenyEllipsoidL2 n q) := by
  have ha : 0 < (16 * (n * q) : ℝ) := by nlinarith
  have hc : (1 : ℝ) < Real.sqrt 2 * Real.pi / 3 := one_lt_sqrt2_mul_pi_div_three
  have hconst : (16 * (n * q) : ℝ) < (16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3) := by
    simpa [mul_assoc] using (mul_lt_mul_of_pos_left hc ha)
  have hpos : 0 < (16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3 : ℝ) := by
    have hcp : 0 < (Real.sqrt 2 * Real.pi / 3 : ℝ) := by
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by nlinarith)
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    exact mul_pos ha hcp
  have hof :
      ENNReal.ofReal (16 * (n * q) : ℝ) <
        ENNReal.ofReal ((16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3) : ℝ) := by
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 hconst
  simpa [volume_ankenyEllipsoidL2_eq n q hn hq] using hof

