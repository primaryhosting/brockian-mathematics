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

theorem centerRot_apply (x : E) : centerRot • x = cVec + rZ 1 • (x - cVec) := by
  show cVec + rZ 1 • (-cVec + x) = cVec + rZ 1 • (x - cVec)
  rw [show (-cVec + x : E) = x - cVec by abel]

