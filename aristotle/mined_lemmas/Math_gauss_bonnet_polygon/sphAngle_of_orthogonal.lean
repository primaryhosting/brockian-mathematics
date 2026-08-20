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

lemma sphAngle_of_orthogonal (u v w : E3) (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0)
    (hvw : ⟪v, w⟫ = 0) : sphAngle u v w = π / 2 := by
  rw [sphAngle, huv, huw]
  simp only [zero_smul, sub_zero]
  exact (inner_eq_zero_iff_angle_eq_pi_div_two v w).1 hvw

/-- The spherical triangle cut out by the standard basis vectors (an octant of the unit
sphere) has area `π / 2`, one eighth of the area `4 * π` of the whole sphere. -/
