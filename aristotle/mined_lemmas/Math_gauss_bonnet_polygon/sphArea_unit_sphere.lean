import RequestProject.Sector

/-!
# Volume of a wedge in three-dimensional space

The main result of this file is `SphericalArea.volume_wedge`: for a unit vector `u` and two
linearly independent vectors `s`, `t` orthogonal to `u`, the set of points of the open unit ball
whose orthogonal projection to `u^⊥` lies in the double wedge spanned by `s` and `t` has volume
`4 * angle s t / 3`.
-/

open MeasureTheory Real Set Metric InnerProductGeometry
open scoped ENNReal Real RealInnerProductSpace

namespace SphericalArea

/-- Coordinates of `EuclideanSpace ℝ (Fin 3)` as a product `ℝ × (ℝ × ℝ)`. -/

lemma sphArea_unit_sphere : sphArea (sphere (0 : E3) 1) = 4 * π := by
  rw [sphArea, coneOver_sphere, measure_diff_null (measure_singleton 0), volume_unit_ball,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-! ### The wedge at a vertex -/

