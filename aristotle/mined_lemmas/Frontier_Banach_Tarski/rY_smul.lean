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

theorem rY_smul (t : ℝ) (x : E) (i : Fin 3) :
    (rY t • x) i = (rotY t) i 0 * x 0 + (rotY t) i 1 * x 1 + (rotY t) i 2 * x 2 := by
  show ∑ j, (rotY t) i j * x j = _
  rw [Fin.sum_univ_three]

/-- A rotation about the `y`-axis fixing a point off the axis must be trivial. -/
