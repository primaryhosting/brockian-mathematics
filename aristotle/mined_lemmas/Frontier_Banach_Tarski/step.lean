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

def step (x : Fin 2 × Bool) (u : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if x.1 = 0 then (u.1 - 4 * sgn x.2 * u.2.1, 2 * sgn x.2 * u.1 + u.2.1, 3 * u.2.2)
  else (3 * u.1, u.2.1 - 2 * sgn x.2 * u.2.2, 4 * sgn x.2 * u.2.1 + u.2.2)

/-- The state reached by applying the word `L` (from right to left) to `(0, 1, 0)`. -/
