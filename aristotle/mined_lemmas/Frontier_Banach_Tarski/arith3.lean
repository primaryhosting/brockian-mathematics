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

theorem arith3 (b c s : ℤ) (hs : s = 1 ∨ s = -1) (hb : ¬ ((3:ℤ) ∣ b))
    (h : (c - s * b) % 3 = 0 ∨ c % 3 = 0) : ¬ ((3:ℤ) ∣ (b - 2 * s * c)) := by
  rcases hs with rfl | rfl <;> omega

