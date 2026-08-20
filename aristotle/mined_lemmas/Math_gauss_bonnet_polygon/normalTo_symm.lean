import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma normalTo_symm (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (h : Indep3 A B C) :
    normalTo A B C = normalTo B A C := by
  set N1 := normalTo A B C with hN1
  set N2 := normalTo B A C with hN2
  have hspan : ∃ s t : ℝ, N1 - N2 = s • A + t • B := by
    refine ⟨(⟪C - ⟪A, C⟫ • A, B - ⟪A, B⟫ • A⟫ / ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫) * ⟪A, B⟫
        - ⟪A, C⟫ + (⟪C - ⟪B, C⟫ • B, A - ⟪B, A⟫ • B⟫ / ⟪A - ⟪B, A⟫ • B, A - ⟪B, A⟫ • B⟫),
      ⟪B, C⟫ - (⟪C - ⟪A, C⟫ • A, B - ⟪A, B⟫ • A⟫ / ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫)
        - (⟪C - ⟪B, C⟫ • B, A - ⟪B, A⟫ • B⟫ / ⟪A - ⟪B, A⟫ • B, A - ⟪B, A⟫ • B⟫) * ⟪B, A⟫, ?_⟩
    rw [hN1, hN2, normalTo, normalTo]
    module
  obtain ⟨s, t, hst⟩ := hspan
  have hA1 : ⟪N1 - N2, A⟫ = 0 := by
    rw [inner_sub_left, normalTo_inner_fst hA, normalTo_inner_snd hB h.perm₁]
    ring
  have hB1 : ⟪N1 - N2, B⟫ = 0 := by
    rw [inner_sub_left, normalTo_inner_snd hA h, normalTo_inner_fst hB]
    ring
  have : ⟪N1 - N2, N1 - N2⟫ = 0 := by
    nth_rewrite 2 [hst]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hA1, hB1]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp this)

