import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma normalTo_inner_fst (hA : ‖A‖ = 1) : ⟪normalTo A B C, A⟫ = 0 := by
  rw [normalTo, inner_sub_left, real_inner_smul_left, inner_tangent_left hA,
    inner_tangent_left hA]
  ring

