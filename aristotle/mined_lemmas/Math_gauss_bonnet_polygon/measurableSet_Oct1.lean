import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma measurableSet_Oct1 (s : ℝ) : MeasurableSet (Oct1 nA s) :=
  measurableSet_unitBall3.inter (measurableSet_halfspace s nA)

