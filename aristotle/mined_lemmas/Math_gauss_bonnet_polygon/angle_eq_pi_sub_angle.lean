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

theorem angle_eq_pi_sub_angle {x y z t : E3} (hnum : (inner ℝ x y : ℝ) = -inner ℝ z t)
    (h1 : ‖x‖ = ‖z‖) (h2 : ‖y‖ = ‖t‖) : angle x y = π - angle z t := by
  rw [angle, angle, hnum, h1, h2, neg_div, Real.arccos_neg]

/-- If `v` vanishes on `x` while `u` does not, and `v` is not zero, then `v` is not a multiple
of `u`. -/
