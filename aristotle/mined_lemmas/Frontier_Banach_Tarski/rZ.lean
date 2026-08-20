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

def rZ (t : ℝ) : SO3 := ⟨rotZ t, rotZ_mem t⟩

/-- Rotation about the `y`-axis, as an element of `SO(3)`. -/
