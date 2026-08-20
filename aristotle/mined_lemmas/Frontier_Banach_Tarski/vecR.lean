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

noncomputable def vecR (u : ℤ × ℤ × ℤ) : Fin 3 → ℝ :=
  ![(u.1 : ℝ), (u.2.1 : ℝ) * Real.sqrt 2, (u.2.2 : ℝ)]

