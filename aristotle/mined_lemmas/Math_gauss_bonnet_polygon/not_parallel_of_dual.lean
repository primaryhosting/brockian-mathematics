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

theorem not_parallel_of_dual {u v x y : E3} {d : ℝ} (hd : d ≠ 0)
    (hux : (inner ℝ u x : ℝ) = d) (hvx : (inner ℝ v x : ℝ) = 0) (hvy : (inner ℝ v y : ℝ) = d) :
    ∀ r : ℝ, v ≠ r • u := by
  intro r hr
  have h0 : (0 : ℝ) = r * d := by rw [← hvx, hr, real_inner_smul_left, hux]
  have hr0 : r = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exact h
    · exact absurd h hd
  rw [hr0, zero_smul] at hr
  rw [hr] at hvy
  simp only [inner_zero_left] at hvy
  exact hd hvy.symm

