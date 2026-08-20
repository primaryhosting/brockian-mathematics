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

theorem rZ_pow (t : ℝ) (n : ℕ) : rZ t ^ n = rZ (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, rZ_zero]
  | succ m ih =>
      rw [pow_succ, ih, ← rZ_add]
      congr 1
      push_cast
      ring

