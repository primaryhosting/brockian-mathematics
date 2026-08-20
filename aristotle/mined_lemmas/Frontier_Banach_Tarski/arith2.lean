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

theorem arith2 (a b c s : ℤ) (hs : s = 1 ∨ s = -1) :
    ((a - 4 * s * b) + s * (2 * s * a + b)) % 3 = 0 ∧ (3 * c) % 3 = 0 := by
  rcases hs with rfl | rfl <;> omega

