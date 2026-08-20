import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma Oct2_subset (s t : ℝ) : Oct2 nA nB s t ⊆ unitBall3 :=
  inter_subset_left.trans (Oct1_subset nA s)

