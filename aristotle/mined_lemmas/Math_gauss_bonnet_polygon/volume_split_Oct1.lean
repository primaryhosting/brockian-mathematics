import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_split_Oct1 (hnB : nB ≠ 0) (s : ℝ) :
    volume (Oct1 nA s) = volume (Oct2 nA nB s 1) + volume (Oct2 nA nB s (-1)) :=
  volume_split' _ (measurableSet_Oct1 nA s) nB hnB

