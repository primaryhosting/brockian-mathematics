import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_split_ball (hnA : nA ≠ 0) :
    volume unitBall3 = volume (Oct1 nA 1) + volume (Oct1 nA (-1)) :=
  volume_split' unitBall3 measurableSet_unitBall3 nA hnA

