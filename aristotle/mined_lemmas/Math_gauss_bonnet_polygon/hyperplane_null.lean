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

theorem hyperplane_null {n : E3} (hn : n ≠ 0) : volume {x : E3 | inner ℝ n x = 0} = 0 := by
  have hset : {x : E3 | inner ℝ n x = 0} = ((ℝ ∙ n)ᗮ : Submodule ℝ E3) := by
    ext x
    simp [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [hset]
  apply Measure.addHaar_submodule
  intro h
  have hmem : n ∈ (ℝ ∙ n)ᗮ := h ▸ Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact hn (inner_self_eq_zero.1 hmem)

/-- Splitting a measurable set by a hyperplane through the origin. -/
