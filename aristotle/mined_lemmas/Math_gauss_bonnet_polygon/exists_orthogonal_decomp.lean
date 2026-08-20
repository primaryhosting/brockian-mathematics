import RequestProject.GaussBonnet.WedgeGeneral
import RequestProject.GaussBonnet.Angle
import RequestProject.GaussBonnet.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

**Girard's theorem** (the Gauss–Bonnet theorem for a geodesic triangle on the unit sphere):
the sum of the three interior angles of a spherical triangle exceeds `π` by its area.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- The inward normal to the side `BC` of the spherical triangle `ABC`, normalised so that
`⟪A, nrm A B C⟫ = 1`. -/

lemma exists_orthogonal_decomp (u v : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ w : E3, ‖w‖ = 1 ∧ ⟪u, w⟫ = 0 ∧ v = cos (angle u v) • u + sin (angle u v) • w := by
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
  have hex : ∃ w : E3, ‖w‖ = 1 ∧ ⟪u, w⟫ = 0 := by
    haveI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
    have hf : Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E3) = 2 :=
      Submodule.finrank_orthogonal_span_singleton hu0
    have hne : ((ℝ ∙ u)ᗮ : Submodule ℝ E3) ≠ ⊥ := by
      intro h; rw [h] at hf; simp at hf
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hip : ⟪u, p⟫ = 0 := by
      rw [Submodule.mem_orthogonal] at hp
      exact hp u (Submodule.mem_span_singleton_self u)
    exact ⟨‖p‖⁻¹ • p, by rw [norm_smul]; simp [norm_ne_zero_iff.2 hp0],
      by rw [real_inner_smul_right, hip, mul_zero]⟩
  set f := angle u v with hf
  have hcos : cos f = ⟪u, v⟫ := by rw [hf, cos_angle, hu, hv]; ring
  have hf0 : 0 ≤ f := angle_nonneg u v
  have hfpi : f ≤ π := angle_le_pi u v
  have hsin : sin f = ‖v - ⟪u, v⟫ • u‖ := by
    have h1 : ‖v - ⟪u, v⟫ • u‖ ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, hv, real_inner_comm u v]
      simp
      ring
    rw [Real.sin_eq_sqrt_one_sub_cos_sq hf0 hfpi, hcos, ← h1, Real.sqrt_sq (norm_nonneg _)]
  by_cases hz : sin f = 0
  · obtain ⟨w, hw1, hw2⟩ := hex
    refine ⟨w, hw1, hw2, ?_⟩
    rw [hz, zero_smul, add_zero, hcos]
    have h3 : ‖v - ⟪u, v⟫ • u‖ = 0 := by rw [← hsin, hz]
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)
  · refine ⟨(sin f)⁻¹ • (v - ⟪u, v⟫ • u), ?_, ?_, ?_⟩
    · rw [norm_smul, ← hsin]
      simp [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hf0 hfpi), hz]
    · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu]
      simp
    · rw [smul_smul, mul_inv_cancel₀ hz, one_smul, hcos]
      module

/-- The standard wedge is measurable. -/
