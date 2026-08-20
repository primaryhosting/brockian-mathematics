import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma volume_ankenyEllipsoidL2_q1_eq (n q : ℝ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankenyEllipsoidL2_q1 n q) =
      ENNReal.ofReal (8 * (n * q) * (Real.pi / 3)) := by
  -- Copy the structure of `volume_ankenyEllipsoidL2_eq`, but with radius `sqrt(2*n*q)`.
  have hdet_pos : 0 < LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := by
    have hsq2 : 0 < Real.sqrt (2 * q) := Real.sqrt_pos.2 (by nlinarith)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by nlinarith)
    have h1 : (0 : ℝ) < 1 := by norm_num
    simpa [det_ankenyDiagMap, mul_assoc, mul_left_comm, mul_comm] using mul_pos (mul_pos hsq2 h1) hsn
  have hdet_ne0 : LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) ≠ 0 := ne_of_gt hdet_pos

  have hr_pos : 0 < ankenyBallRadius_q1 n q := by
    have : 0 < 2 * (n * q) := by nlinarith
    simpa [ankenyBallRadius_q1] using Real.sqrt_pos.2 this

  have hpre :
      volume (ankenyEllipsoidL2_q1 n q) =
        ENNReal.ofReal |(LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹| *
          volume (l2Ball (ankenyBallRadius_q1 n q)) := by
    simpa [ankenyEllipsoidL2_q1] using
      (MeasureTheory.Measure.addHaar_preimage_linearMap
        (μ := (volume : Measure E3))
        (f := GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
        hdet_ne0
        (l2Ball (ankenyBallRadius_q1 n q)))

  have hdet_abs_inv :
      ENNReal.ofReal |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)|⁻¹
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) := by
    have habs : |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)| =
        LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := abs_of_pos hdet_pos
    simp [habs]

  have hr_nn : 0 ≤ ankenyBallRadius_q1 n q := le_of_lt hr_pos
  have hdet_nn : 0 ≤ (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ :=
    le_of_lt (inv_pos.2 hdet_pos)
  have hpi_nn : 0 ≤ (Real.pi * 4 / 3 : ℝ) := by
    have : 0 < (Real.pi : ℝ) := Real.pi_pos
    nlinarith

  -- Determinant simplification: in this regime, `det = sqrt(2*n*q)` equals the chosen radius.
  have hdet_eq_r :
      LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) = ankenyBallRadius_q1 n q := by
    have hnq_nn : (0 : ℝ) ≤ n * q := by nlinarith [le_of_lt hn, le_of_lt hq]
    have h2_nn : (0 : ℝ) ≤ (2 : ℝ) := by nlinarith
    have hr : ankenyBallRadius_q1 n q = Real.sqrt 2 * Real.sqrt (n * q) := by
      -- `sqrt(2*(n*q)) = sqrt 2 * sqrt(n*q)`
      simpa [ankenyBallRadius_q1, mul_assoc] using (Real.sqrt_mul h2_nn (n * q))
    have hn_nn : (0 : ℝ) ≤ n := le_of_lt hn
    have hq_nn : (0 : ℝ) ≤ q := le_of_lt hq
    have hsq : Real.sqrt (n * q) = Real.sqrt n * Real.sqrt q := by
      simpa [mul_comm] using (Real.sqrt_mul hn_nn q)
    -- `det = sqrt(2q) * sqrt(n) = sqrt 2 * sqrt(q) * sqrt(n)`
    have hdet' : LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) = Real.sqrt 2 * Real.sqrt q * Real.sqrt n := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using det_ankenyDiagMap n q
    -- rewrite both sides to the same commutative product
    calc
      LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
          = Real.sqrt 2 * (Real.sqrt n * Real.sqrt q) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hdet'
      _ = Real.sqrt 2 * Real.sqrt (n * q) := by
              simpa [hsq, mul_assoc, mul_left_comm, mul_comm]
      _ = ankenyBallRadius_q1 n q := by simpa [hr, mul_assoc, mul_left_comm, mul_comm]

  -- Radius square: `r^2 = 2*(n*q)`.
  have hr2 : (ankenyBallRadius_q1 n q) ^ 2 = 2 * (n * q) := by
    have hnq_nn : 0 ≤ 2 * (n * q) := by nlinarith [le_of_lt hn, le_of_lt hq]
    -- use `sq_sqrt` directly to avoid rewriting `sqrt(2*(n*q))` into products of square roots
    simpa [ankenyBallRadius_q1] using (Real.sq_sqrt hnq_nn)

  -- Now combine.
  calc
    volume (ankenyEllipsoidL2_q1 n q)
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
            volume (l2Ball (ankenyBallRadius_q1 n q)) := by
            simpa [hpre, abs_inv, hdet_abs_inv]
    _ = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
          ((ENNReal.ofReal (ankenyBallRadius_q1 n q)) ^ 3 *
            ENNReal.ofReal (Real.pi * 4 / 3)) := by
          simp [volume_l2Ball]
    _ = ENNReal.ofReal (
            ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((ankenyBallRadius_q1 n q) ^ 3) *
              (Real.pi * 4 / 3)
          ) := by
          simp [ENNReal.ofReal_mul, hr_nn, hpi_nn, mul_assoc, mul_comm]
    _ = ENNReal.ofReal (8 * (n * q) * (Real.pi / 3)) := by
          -- core: det^{-1} * r^3 = 2*(n*q)
          have hs_pos : 0 < ankenyBallRadius_q1 n q := hr_pos
          have hs_ne0 : ankenyBallRadius_q1 n q ≠ 0 := ne_of_gt hs_pos
          have hcore :
              (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3)
                = 2 * (n * q) := by
            -- Since `det = r`, this is `r⁻¹ * r^3 = r^2`.
            calc
              (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3)
                  = (ankenyBallRadius_q1 n q)⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3) := by
                      simp [hdet_eq_r]
              _ = (ankenyBallRadius_q1 n q) ^ 2 := by
                      -- `r⁻¹ * r^3 = (r⁻¹*r) * r^2 = r^2`
                      calc
                        (ankenyBallRadius_q1 n q)⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3)
                            = (ankenyBallRadius_q1 n q)⁻¹ * ((ankenyBallRadius_q1 n q) ^ 2 * ankenyBallRadius_q1 n q) := by
                                  simp [pow_succ, mul_assoc]
                        _ = ((ankenyBallRadius_q1 n q)⁻¹ * ankenyBallRadius_q1 n q) * ((ankenyBallRadius_q1 n q) ^ 2) := by
                                  simp [mul_assoc, mul_left_comm, mul_comm]
                        _ = (ankenyBallRadius_q1 n q) ^ 2 := by
                                  simp [hs_ne0]
              _ = 2 * (n * q) := by simpa [hr2]
          -- multiply by `pi*4/3`
          have : ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((ankenyBallRadius_q1 n q) ^ 3) * (Real.pi * 4 / 3)
              = 8 * (n * q) * (Real.pi / 3) := by
            calc
              ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
                  ((ankenyBallRadius_q1 n q) ^ 3) * (Real.pi * 4 / 3)
                  = (2 * (n * q)) * (Real.pi * 4 / 3) := by simpa [hcore]
              _ = 8 * (n * q) * (Real.pi / 3) := by ring
          simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg ENNReal.ofReal this

