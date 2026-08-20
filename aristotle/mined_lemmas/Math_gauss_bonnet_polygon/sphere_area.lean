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

theorem sphere_area : (volume.toSphere (univ : Set (sphere (0 : E3) 1))).toReal = 4 * π := by
  rw [Measure.toSphere_apply_univ, volume_unit_ball,
    show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp
  ring

/-- The area of the spherical octant spanned by the three standard basis vectors is `π / 2`,
one eighth of the area of the sphere. -/
