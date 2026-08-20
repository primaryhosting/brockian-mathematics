import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma measurableSet_Oct3 (s t u : ℝ) : MeasurableSet (Oct3 nA nB nC s t u) :=
  (measurableSet_Oct2 nA nB s t).inter (measurableSet_halfspace u nC)

