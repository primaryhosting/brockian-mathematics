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

theorem rY_fix (t : ℝ) (x : E) (hx : x 0 ≠ 0 ∨ x 2 ≠ 0) (h : rY t • x = x) :
    Real.cos t = 1 ∧ Real.sin t = 0 := by
  have h0 : (rY t • x) 0 = x 0 := by rw [h]
  have h2 : (rY t • x) 2 = x 2 := by rw [h]
  rw [rY_smul] at h0 h2
  simp only [rotY, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.vecHead] at h0 h2
  have hpos : 0 < x 0 ^ 2 + x 2 ^ 2 := by
    rcases hx with hne | hne
    · have := sq_nonneg (x 2); positivity
    · have := sq_nonneg (x 0); positivity
  constructor
  · have hkey : (Real.cos t - 1) * (x 0 ^ 2 + x 2 ^ 2) = 0 := by
      linear_combination (x 0) * h0 + (x 2) * h2
    have := (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)
    linarith
  · have hkey : Real.sin t * (x 0 ^ 2 + x 2 ^ 2) = 0 := by
      linear_combination (x 2) * h0 - (x 0) * h2
    exact (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)

/-- Points of the sphere off the `z`-axis. -/
