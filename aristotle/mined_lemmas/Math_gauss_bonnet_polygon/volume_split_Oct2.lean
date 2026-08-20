import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_split_Oct2 (hnC : nC ≠ 0) (s t : ℝ) :
    volume (Oct2 nA nB s t) = volume (Oct3 nA nB nC s t 1) + volume (Oct3 nA nB nC s t (-1)) :=
  volume_split' _ (measurableSet_Oct2 nA nB s t) nC hnC

/-- A wedge, described as an intersection. -/
