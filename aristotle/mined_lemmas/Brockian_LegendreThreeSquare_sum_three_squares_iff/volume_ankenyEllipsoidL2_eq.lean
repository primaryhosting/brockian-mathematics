import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma volume_ankenyEllipsoidL2_eq (n q : ℝ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankenyEllipsoidL2 n q) =
      ENNReal.ofReal ((16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3)) := by
  have hdet_pos : 0 < LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := by
    have hsq2 : 0 < Real.sqrt (2 * q) := Real.sqrt_pos.2 (by nlinarith)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by nlinarith)
    have h1 : (0 : ℝ) < 1 := by norm_num
    simpa [det_ankenyDiagMap, mul_assoc, mul_left_comm, mul_comm] using mul_pos (mul_pos hsq2 h1) hsn
  have hdet_ne0 : LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) ≠ 0 := ne_of_gt hdet_pos

  have hr_pos : 0 < GeometryOfNumbers.Minkowski.ankenyBallRadius n q := by
    have hs : 0 < Real.sqrt (n * q) := Real.sqrt_pos.2 (by nlinarith)
    have h2 : (0 : ℝ) < 2 := by norm_num
    simpa [GeometryOfNumbers.Minkowski.ankenyBallRadius] using mul_pos h2 hs

  have hpre :
      volume (ankenyEllipsoidL2 n q) =
        ENNReal.ofReal |(LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹| *
          volume (l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)) := by
    simpa [ankenyEllipsoidL2] using
      (MeasureTheory.Measure.addHaar_preimage_linearMap
        (μ := (volume : Measure E3))
        (f := GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
        hdet_ne0
        (l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)))

  have hdet_abs_inv :
      ENNReal.ofReal |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)|⁻¹
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) := by
    -- `|det| = det` since `det > 0`, hence `|det|⁻¹ = det⁻¹`.
    have habs : |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)| =
        LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := abs_of_pos hdet_pos
    simp [habs]

  -- Reduce to a real identity under `ENNReal.ofReal`.
  calc
    volume (ankenyEllipsoidL2 n q)
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
            volume (l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)) := by
            -- `|(det)⁻¹| = |det|⁻¹` and `|det| = det` by positivity.
            simpa [hpre, abs_inv, hdet_abs_inv]
    _ = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
          ((ENNReal.ofReal (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)) ^ 3 *
            ENNReal.ofReal (Real.pi * 4 / 3)) := by
          simp [volume_l2Ball]
    _ = ENNReal.ofReal (
            ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3) *
              (Real.pi * 4 / 3)
          ) := by
          have hdet_nn : 0 ≤ (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ :=
            le_of_lt (inv_pos.2 hdet_pos)
          have hr_nn : 0 ≤ (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) := le_of_lt hr_pos
          have hpi_nn : 0 ≤ (Real.pi * 4 / 3 : ℝ) := by
            have : 0 < (Real.pi : ℝ) := Real.pi_pos
            nlinarith
          simp [ENNReal.ofReal_mul, hr_nn, hpi_nn, mul_assoc, mul_comm]
    _ = ENNReal.ofReal ((16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3)) := by
          have hdet :
              LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) =
                Real.sqrt (2 * q) * Real.sqrt n := by
            simpa [mul_assoc] using det_ankenyDiagMap n q
          have hr3 :
              (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3 =
                8 * (n * q) * Real.sqrt (n * q) := ankenyBallRadius_pow_three n q (by nlinarith : 0 ≤ n * q)
          have hsq_mul : Real.sqrt (n * q) = Real.sqrt n * Real.sqrt q := by
            have hn_nn : 0 ≤ n := le_of_lt hn
            simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.sqrt_mul hn_nn q)
          have hsq2q : Real.sqrt (2 * q) = Real.sqrt 2 * Real.sqrt q := by
            have h2_nn : 0 ≤ (2 : ℝ) := by nlinarith
            simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.sqrt_mul h2_nn q)
          have hsqn_ne0 : Real.sqrt n ≠ 0 := by
            exact ne_of_gt (Real.sqrt_pos.2 (by linarith))
          have hsqrtq_ne0 : Real.sqrt q ≠ 0 := by
            exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith))
          have hsq2q_ne0 : Real.sqrt (2 * q) ≠ 0 := by
            exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith))
          have : ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3) * (Real.pi * 4 / 3)
                = (16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3) := by
            -- Substitute closed forms and cancel square roots (as in the experiment file).
            simp [hdet, hr3, hsq_mul, mul_assoc, mul_left_comm, mul_comm] at *
            -- `field_simp` clears denominators and may leave a side-condition goal.
            field_simp [hsqn_ne0, hsq2q_ne0]
            ring_nf
            -- Side condition from `field_simp` (guarded denominators / clearing).
            left
            left
            have hs : (Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ) := by
              -- `2 ≥ 0`, so `sqrt(2)^2 = 2`.
              simpa [pow_two] using (Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ (2 : ℝ)))
            -- `32 = 2 * 16 = sqrt(2)^2 * 16`
            nlinarith
          simpa [this]

