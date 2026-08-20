import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem wedge_frame (a p q : E3) (hp : ⟪a, p⟫ = 0) (hq : ⟪a, q⟫ = 0)
    (hpq : LinearIndependent ℝ ![p, q]) :
    ∃ b1 b2 : E3, ‖b1‖ = 1 ∧ ‖b2‖ = 1 ∧ ⟪a, b1⟫ = 0 ∧ ⟪a, b2⟫ = 0 ∧ ⟪b1, b2⟫ = 0 ∧
      p = ‖p‖ • b1 ∧
      q = (‖q‖ * Real.cos (angle p q)) • b1 + (‖q‖ * Real.sin (angle p q)) • b2 := by
  have hp0 : p ≠ 0 := hpq.ne_zero 0
  have hq0 : q ≠ 0 := hpq.ne_zero 1
  have hnp : 0 < ‖p‖ := norm_pos_iff.2 hp0
  have hnq : 0 < ‖q‖ := norm_pos_iff.2 hq0
  have hsin : 0 < Real.sin (angle p q) := sin_angle_pos p q hpq
  obtain ⟨b1, hb1def⟩ : ∃ v : E3, v = ‖p‖⁻¹ • p := ⟨_, rfl⟩
  have hb1 : ‖b1‖ = 1 := by
    rw [hb1def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnp.ne']
  have hb1b1 : ⟪b1, b1⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hb1]; norm_num
  have hab1 : ⟪a, b1⟫ = (0 : ℝ) := by rw [hb1def, real_inner_smul_right, hp, mul_zero]
  have hpb1 : p = ‖p‖ • b1 := by
    rw [hb1def, smul_smul, mul_inv_cancel₀ hnp.ne', one_smul]
  have hc : ⟪b1, q⟫ = ‖q‖ * Real.cos (angle p q) := by
    rw [hb1def, real_inner_smul_left, ← cos_angle_mul_norm_mul_norm p q]
    field_simp
  have hc' : ⟪q, b1⟫ = ‖q‖ * Real.cos (angle p q) := by rw [real_inner_comm]; exact hc
  obtain ⟨w, hwdef⟩ : ∃ v : E3, v = q - (‖q‖ * Real.cos (angle p q)) • b1 := ⟨_, rfl⟩
  have hb1w : ⟪b1, w⟫ = (0 : ℝ) := by
    rw [hwdef, inner_sub_right, hc, real_inner_smul_right, hb1b1]; ring
  have haw : ⟪a, w⟫ = (0 : ℝ) := by
    rw [hwdef, inner_sub_right, hq, real_inner_smul_right, hab1]; ring
  have hww : ⟪w, w⟫ = ‖q‖ ^ 2 * (Real.sin (angle p q)) ^ 2 := by
    have hqq : ⟪q, q⟫ = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
    rw [hwdef]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hc, hc', hb1b1, hqq]
    have := Real.sin_sq_add_cos_sq (angle p q)
    nlinarith
  have hnw : ‖w‖ = ‖q‖ * Real.sin (angle p q) := by
    have h1 : ‖w‖ ^ 2 = (‖q‖ * Real.sin (angle p q)) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hww]; ring
    have hnn : 0 ≤ ‖q‖ * Real.sin (angle p q) := by positivity
    nlinarith [norm_nonneg w]
  have hnw0 : 0 < ‖w‖ := by rw [hnw]; positivity
  obtain ⟨b2, hb2def⟩ : ∃ v : E3, v = ‖w‖⁻¹ • w := ⟨_, rfl⟩
  refine ⟨b1, b2, hb1, ?_, hab1, ?_, ?_, hpb1, ?_⟩
  · rw [hb2def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw0.ne']
  · rw [hb2def, real_inner_smul_right, haw, mul_zero]
  · rw [hb2def, real_inner_smul_right, hb1w, mul_zero]
  · rw [← hnw, hb2def, smul_smul, mul_inv_cancel₀ hnw0.ne', one_smul, hwdef]
    abel

/-- The volume of a solid wedge inside the unit ball, in terms of an adapted orthonormal
frame `a, b1, b2`. -/
