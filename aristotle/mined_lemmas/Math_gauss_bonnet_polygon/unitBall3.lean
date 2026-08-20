import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

def unitBall3 : Set E3 := {x : E3 | ‖x‖ ≤ 1}

section

variable (nA nB nC : E3)

/-- The part of the unit ball on the side `s` of the plane normal to `nA`. -/
