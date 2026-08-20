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

theorem ne_zero_of_inner_ne_zero {u x : E3} {d : ℝ} (hd : d ≠ 0) (hux : (inner ℝ u x : ℝ) = d) :
    u ≠ 0 := by
  intro h
  rw [h] at hux
  simp only [inner_zero_left] at hux
  exact hd hux.symm

/-! ### The area of a spherical triangle in terms of the dual frame -/

section DualFrame

variable {a b c u v w : E3} {d : ℝ}

/-- Membership in the cone spanned by `a`, `b`, `c`, in terms of the dual frame. -/
