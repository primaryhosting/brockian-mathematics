import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma inner_self_of_norm_one (hA : ‖A‖ = 1) : ⟪A, A⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hA]; norm_num

