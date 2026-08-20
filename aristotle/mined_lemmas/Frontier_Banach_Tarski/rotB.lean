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

noncomputable def rotB : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, 1/3, -(2 * Real.sqrt 2)/3;
     0, (2 * Real.sqrt 2)/3, 1/3]

