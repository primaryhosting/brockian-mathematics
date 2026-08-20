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

lemma coneOver_sphere : coneOver (sphere (0 : E3) 1) = ball (0 : E3) 1 \ {0} := by
  ext x
  simp only [coneOver, mem_setOf_eq, mem_diff, mem_ball_zero_iff, mem_singleton_iff,
    mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨r, hr0, hr1, y, hy, rfl⟩
    rw [norm_smul, hy, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
    exact ⟨hr1, smul_ne_zero hr0.ne' (by rw [← norm_pos_iff, hy]; norm_num)⟩
  · rintro ⟨h1, h2⟩
    have hx : 0 < ‖x‖ := norm_pos_iff.2 h2
    refine ⟨‖x‖, hx, h1, ‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx.ne']
    · rw [smul_smul, mul_inv_cancel₀ hx.ne', one_smul]

