import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma solidCone_triangle (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hind : LinearIndependent ℝ ![A, B, C]) :
    solidCone (sphericalTriangle A B C)
      = Oct3 (normalTo B C A) (normalTo C A B) (normalTo A B C) 1 1 1 := by
  have h3 : Indep3 A B C := indep3_of_linearIndependent hind
  set nA := normalTo B C A with hnAdef
  set nB := normalTo C A B with hnBdef
  set nC := normalTo A B C with hnCdef
  have hAnA : ⟪A, nA⟫ = ⟪nA, nA⟫ := by
    rw [real_inner_comm]; exact normalTo_inner_trd hB h3.rot
  have hBnA : ⟪B, nA⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_fst hB
  have hCnA : ⟪C, nA⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_snd hB h3.rot
  have hBnB : ⟪B, nB⟫ = ⟪nB, nB⟫ := by
    rw [real_inner_comm]; exact normalTo_inner_trd hC h3.rot.rot
  have hCnB : ⟪C, nB⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_fst hC
  have hAnB : ⟪A, nB⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_snd hC h3.rot.rot
  have hCnC : ⟪C, nC⟫ = ⟪nC, nC⟫ := by rw [real_inner_comm]; exact normalTo_inner_trd hA h3
  have hAnC : ⟪A, nC⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_fst hA
  have hBnC : ⟪B, nC⟫ = 0 := by rw [real_inner_comm]; exact normalTo_inner_snd hA h3
  have pA : 0 < ⟪nA, nA⟫ := real_inner_self_pos.mpr (normalTo_ne_zero h3.rot)
  have pB : 0 < ⟪nB, nB⟫ := real_inner_self_pos.mpr (normalTo_ne_zero h3.rot.rot)
  have pC : 0 < ⟪nC, nC⟫ := real_inner_self_pos.mpr (normalTo_ne_zero h3)
  have expA : ∀ a b c : ℝ, ⟪a • A + b • B + c • C, nA⟫ = a * ⟪nA, nA⟫ := by
    intro a b c
    simp only [inner_add_left, real_inner_smul_left, hAnA, hBnA, hCnA]
    ring
  have expB : ∀ a b c : ℝ, ⟪a • A + b • B + c • C, nB⟫ = b * ⟪nB, nB⟫ := by
    intro a b c
    simp only [inner_add_left, real_inner_smul_left, hAnB, hBnB, hCnB]
    ring
  have expC : ∀ a b c : ℝ, ⟪a • A + b • B + c • C, nC⟫ = c * ⟪nC, nC⟫ := by
    intro a b c
    simp only [inner_add_left, real_inner_smul_left, hAnC, hBnC, hCnC]
    ring
  ext x
  simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul, solidCone,
    sphericalTriangle]
  constructor
  · rintro ⟨t, ht0, ht1, y, ⟨hy1, a, b, c, ha, hb, hc, rfl⟩, rfl⟩
    have hnorm : ‖t • (a • A + b • B + c • C)‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hy1, mul_one]
      exact ht1
    refine ⟨⟨⟨hnorm, ?_⟩, ?_⟩, ?_⟩
    · rw [real_inner_smul_left, expA]
      positivity
    · rw [real_inner_smul_left, expB]
      positivity
    · rw [real_inner_smul_left, expC]
      positivity
  · rintro ⟨⟨⟨hnorm, h1⟩, h2⟩, h3'⟩
    obtain ⟨a, b, c, rfl⟩ := exists_repr hind x
    rw [expA] at h1
    rw [expB] at h2
    rw [expC] at h3'
    have ha : 0 ≤ a := nonneg_of_mul_nonneg_left h1 pA
    have hb : 0 ≤ b := nonneg_of_mul_nonneg_left h2 pB
    have hc : 0 ≤ c := nonneg_of_mul_nonneg_left h3' pC
    rcases eq_or_ne (a • A + b • B + c • C) 0 with hx0 | hx0
    · refine ⟨0, le_refl _, zero_le_one, A, ⟨hA, 1, 0, 0, zero_le_one, le_refl _, le_refl _,
        by module⟩, ?_⟩
      rw [hx0, zero_smul]
    · refine ⟨‖a • A + b • B + c • C‖, norm_nonneg _, hnorm,
        ‖a • A + b • B + c • C‖⁻¹ • (a • A + b • B + c • C), ⟨?_, ?_⟩, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm]
        field_simp
      · refine ⟨‖a • A + b • B + c • C‖⁻¹ * a, ‖a • A + b • B + c • C‖⁻¹ * b,
          ‖a • A + b • B + c • C‖⁻¹ * c, ?_, ?_, ?_, by module⟩
        · positivity
        · positivity
        · positivity
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]

end

/-- **Girard's theorem / Gauss–Bonnet for a spherical triangle.**
The angle sum of a (nondegenerate) geodesic triangle on the unit sphere exceeds `π`
exactly by the area of the triangle. -/
