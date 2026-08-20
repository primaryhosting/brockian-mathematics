import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

def Oct2 (s t : ℝ) : Set E3 := Oct1 nA s ∩ {x | 0 ≤ t * ⟪x, nB⟫}

/-- The part of the unit ball on prescribed sides of the three planes. -/
