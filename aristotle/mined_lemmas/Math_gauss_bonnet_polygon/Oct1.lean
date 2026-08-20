import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

def Oct1 (s : ℝ) : Set E3 := unitBall3 ∩ {x | 0 ≤ s * ⟪x, nA⟫}

/-- The part of the unit ball on prescribed sides of the planes normal to `nA`, `nB`. -/
