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

theorem not_parallel_of_linearIndependent {a b c : E3} (hli : LinearIndependent ℝ ![a, b, c]) :
    ∀ r : ℝ, c ≠ r • b := by
  intro r hr
  have h := Fintype.linearIndependent_iff.1 hli ![0, r, -1] (by simp [Fin.sum_univ_three, hr]) 2
  simp at h

/-- The scalar triple product of three linearly independent vectors is nonzero. -/
