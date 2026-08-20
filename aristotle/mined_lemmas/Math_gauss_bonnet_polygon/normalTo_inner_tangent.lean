import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma normalTo_inner_tangent (h : Indep3 A B C) :
    ⟪normalTo A B C, B - ⟪A, B⟫ • A⟫ = 0 := by
  have hu : B - ⟪A, B⟫ • A ≠ 0 := tangent_ne_zero h
  have huu : ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫ ≠ 0 :=
    ne_of_gt (real_inner_self_pos.mpr hu)
  rw [normalTo, inner_sub_left, real_inner_smul_left]
  field_simp
  ring

