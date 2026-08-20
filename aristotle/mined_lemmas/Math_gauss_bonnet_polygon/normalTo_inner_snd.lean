import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma normalTo_inner_snd (hA : ‖A‖ = 1) (h : Indep3 A B C) : ⟪normalTo A B C, B⟫ = 0 := by
  have hB : ⟪normalTo A B C, B⟫
      = ⟪normalTo A B C, (B - ⟪A, B⟫ • A) + ⟪A, B⟫ • A⟫ := by congr 1; module
  rw [hB, inner_add_right, real_inner_smul_right, normalTo_inner_fst hA,
    normalTo_inner_tangent h]
  ring

