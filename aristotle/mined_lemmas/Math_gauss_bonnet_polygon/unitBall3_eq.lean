import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma unitBall3_eq : unitBall3 = closedBall (0 : E3) 1 := by ext x; simp [unitBall3]

