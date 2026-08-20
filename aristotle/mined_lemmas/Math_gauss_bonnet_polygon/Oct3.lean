import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

def Oct3 (s t u : ℝ) : Set E3 := Oct2 nA nB s t ∩ {x | 0 ≤ u * ⟪x, nC⟫}

