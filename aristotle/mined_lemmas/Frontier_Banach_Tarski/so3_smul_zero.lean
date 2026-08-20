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

theorem so3_smul_zero (M : SO3) : M • (0 : E) = 0 := by
  ext i
  show ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (0 : E) j = (0 : E) i
  simp

