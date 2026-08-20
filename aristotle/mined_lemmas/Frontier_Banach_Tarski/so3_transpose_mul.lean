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

theorem so3_transpose_mul (M : SO3) :
    (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (M : Matrix (Fin 3) (Fin 3) ℝ) = 1 := M.2.1.1

