import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem norm_lt_one_iff (x : E3) : ‖x‖ < 1 ↔ (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 < 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [show (1 : ℝ) = √1 by simp, Real.sqrt_lt_sqrt_iff (by positivity)]
  simp

/-- A measurable identification of `ℝ³` with `ℝ × (ℝ × ℝ)`, splitting off the last coordinate. -/
