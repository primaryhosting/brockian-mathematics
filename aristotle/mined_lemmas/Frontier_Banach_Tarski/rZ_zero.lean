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

theorem rZ_zero : rZ 0 = 1 := by
  apply Subtype.ext
  show rotZ 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ]

