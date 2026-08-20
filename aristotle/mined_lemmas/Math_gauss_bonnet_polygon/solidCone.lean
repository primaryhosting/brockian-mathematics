import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

def solidCone (S : Set E3) : Set E3 :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ y ∈ S, x = t • y}

/-- The area of a region of the unit sphere, defined as three times the volume of the
cone over it.  (The cone over a region of area `a` on the unit sphere has volume `a / 3`.) -/
