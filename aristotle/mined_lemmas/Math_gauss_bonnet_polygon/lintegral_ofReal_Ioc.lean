/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

private theorem lintegral_ofReal_Ioc (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal r = ENNReal.ofReal (R ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le hR]
    simp [integral_id]
  · exact continuous_id.integrableOn_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using hx.1.le

/-- **Area of a circular sector**: for `0 ≤ t ≤ π`, the sector of the disc of radius `R`
cut out by the two half-planes has area `(π - t)/2 * R ^ 2`. -/
