import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_unitBall3_ne_top : volume unitBall3 ≠ ⊤ := by
  rw [volume_unitBall3]; exact ENNReal.ofReal_ne_top

