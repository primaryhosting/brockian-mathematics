import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma measurableSet_Oct2 (s t : ℝ) : MeasurableSet (Oct2 nA nB s t) :=
  (measurableSet_Oct1 nA s).inter (measurableSet_halfspace t nB)

