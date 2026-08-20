import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma normalTo_ne_zero (h : Indep3 A B C) : normalTo A B C ≠ 0 := by
  intro h0
  rw [normalTo, sub_eq_zero] at h0
  exact tangent_not_parallel h _ h0

/-- The normal to the plane through `A` and `B` on the side of `C` does not depend on the
order of `A` and `B`. -/
