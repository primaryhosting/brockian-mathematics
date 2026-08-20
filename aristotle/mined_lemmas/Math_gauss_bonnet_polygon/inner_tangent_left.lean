import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma inner_tangent_left (hA : ‖A‖ = 1) : ⟪B - ⟪A, B⟫ • A, A⟫ = 0 := by
  rw [inner_sub_left, real_inner_smul_left, inner_self_of_norm_one hA, real_inner_comm B A]
  ring

