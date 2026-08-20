import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma Oct3_subset (s t u : ℝ) : Oct3 nA nB nC s t u ⊆ unitBall3 :=
  inter_subset_left.trans (Oct2_subset nA nB s t)

