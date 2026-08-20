/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

def sgn (e : Bool) : ℤ := if e then 1 else -1

/-- One step of the integer state machine: the state `(a, b, c)` represents the vector
`(a, b * √2, c) / 3 ^ k`. -/
