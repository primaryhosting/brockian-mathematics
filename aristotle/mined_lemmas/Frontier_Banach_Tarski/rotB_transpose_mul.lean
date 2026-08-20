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

theorem rotB_transpose_mul : rotBᵀ * rotB = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotB, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [sqrt_two_sq]

