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

theorem rZ_fix (t : ℝ) (x : E) (hx : x 0 ≠ 0 ∨ x 1 ≠ 0) (h : rZ t • x = x) :
    Real.cos t = 1 ∧ Real.sin t = 0 := by
  have h0 : (rZ t • x) 0 = x 0 := by rw [h]
  have h1 : (rZ t • x) 1 = x 1 := by rw [h]
  rw [rZ_smul] at h0 h1
  simp only [rotZ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.tail_cons] at h0 h1
  have hpos : 0 < x 0 ^ 2 + x 1 ^ 2 := by
    rcases hx with hne | hne
    · have := sq_nonneg (x 1); positivity
    · have := sq_nonneg (x 0); positivity
  constructor
  · have hkey : (Real.cos t - 1) * (x 0 ^ 2 + x 1 ^ 2) = 0 := by
      linear_combination (x 0) * h0 + (x 1) * h1
    have := (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)
    linarith
  · have hkey : Real.sin t * (x 0 ^ 2 + x 1 ^ 2) = 0 := by
      linear_combination (-(x 1)) * h0 + (x 0) * h1
    exact (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)

