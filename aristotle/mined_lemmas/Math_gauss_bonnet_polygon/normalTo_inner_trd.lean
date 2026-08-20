import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma normalTo_inner_trd (hA : ‖A‖ = 1) (h : Indep3 A B C) :
    ⟪normalTo A B C, C⟫ = ⟪normalTo A B C, normalTo A B C⟫ := by
  have hC : ⟪normalTo A B C, C⟫
      = ⟪normalTo A B C, (C - ⟪A, C⟫ • A) + ⟪A, C⟫ • A⟫ := by congr 1; module
  have h1 : ⟪normalTo A B C, C⟫ = ⟪normalTo A B C, C - ⟪A, C⟫ • A⟫ := by
    rw [hC, inner_add_right, real_inner_smul_right, normalTo_inner_fst hA]
    ring
  have h2 : ⟪normalTo A B C, normalTo A B C⟫ = ⟪normalTo A B C, C - ⟪A, C⟫ • A⟫ := by
    nth_rewrite 2 [normalTo]
    rw [inner_sub_right, real_inner_smul_right, normalTo_inner_tangent h]
    ring
  rw [h1, h2]

