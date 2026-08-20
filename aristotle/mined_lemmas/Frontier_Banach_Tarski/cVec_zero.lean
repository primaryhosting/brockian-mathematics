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

theorem cVec_zero : cVec 0 = 1 / 2 := by
  simp [cVec, EuclideanSpace.single_apply]

/-- A rotation by a positive whole number of radians about the `z`-axis does not fix `cVec`
(this is where the irrationality of `π` enters). -/
