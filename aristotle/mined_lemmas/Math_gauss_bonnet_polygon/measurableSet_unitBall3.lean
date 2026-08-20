import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma measurableSet_unitBall3 : MeasurableSet unitBall3 := by
  rw [unitBall3_eq]; exact measurableSet_closedBall

