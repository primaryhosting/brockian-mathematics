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

theorem so3_smul_smul (M : SO3) (c : ℝ) (x : E) : M • (c • x) = c • (M • x) := by
  ext i
  show ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (c • x) j
      = c * ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (c * x j) = c * ((M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j)
  ring

/-- A rotation, viewed as an isometry of `ℝ³`. -/
