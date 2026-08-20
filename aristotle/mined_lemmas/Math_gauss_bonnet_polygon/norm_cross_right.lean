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

theorem norm_cross_right (a x : E3) (ha : ‖a‖ = 1) :
    ‖cross x a‖ = ‖x - (inner ℝ a x : ℝ) • a‖ := by
  have hsq : ‖cross x a‖ ^ 2 = ‖x - (inner ℝ a x : ℝ) • a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_cross_cross]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha,
      real_inner_comm a x]
    ring
  rw [show ‖cross x a‖ = √(‖cross x a‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, hsq,
    Real.sqrt_sq (norm_nonneg _)]

/-- `‖a × x‖ = ‖x - ⟪a,x⟫ a‖` for a unit vector `a`. -/
