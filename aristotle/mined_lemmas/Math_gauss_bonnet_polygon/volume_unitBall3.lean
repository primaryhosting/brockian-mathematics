import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_unitBall3 : volume unitBall3 = ENNReal.ofReal (4 * π / 3) := by
  rw [unitBall3_eq]; exact volume_closedBall_E3

