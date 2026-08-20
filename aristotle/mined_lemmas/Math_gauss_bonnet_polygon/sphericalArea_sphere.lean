import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma sphericalArea_sphere : sphericalArea {x : E3 | ‖x‖ = 1} = 4 * π := by
  have hcone : solidCone {x : E3 | ‖x‖ = 1} = closedBall (0 : E3) 1 := by
    ext x
    simp only [solidCone, mem_setOf_eq, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨t, ht0, ht1, y, hy, rfl⟩
      rw [norm_smul, show ‖y‖ = 1 from hy, Real.norm_eq_abs, abs_of_nonneg ht0, mul_one]
      exact ht1
    · intro hx
      rcases eq_or_ne x 0 with rfl | hx0
      · exact ⟨0, le_refl _, zero_le_one, EuclideanSpace.single 0 1, by
          simp [EuclideanSpace.norm_single], by simp⟩
      · refine ⟨‖x‖, norm_nonneg _, hx, ‖x‖⁻¹ • x, ?_, ?_⟩
        · simp only [norm_smul, norm_inv, norm_norm]
          field_simp
        · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]
  rw [sphericalArea, hcone, volume_closedBall_E3,
    ENNReal.toReal_ofReal (by positivity)]
  ring

section

variable {A B C : E3}

/-- The cone over the spherical triangle is the intersection of the unit ball with the three
half-spaces determined by the side normals. -/
