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

theorem rZ_inv (t : ℝ) : (rZ t)⁻¹ = rZ (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← rZ_add, add_neg_cancel, rZ_zero]

