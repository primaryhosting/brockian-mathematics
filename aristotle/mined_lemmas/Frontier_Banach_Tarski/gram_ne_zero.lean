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

theorem gram_ne_zero {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h1 : u ≠ v) (h2 : u ≠ -v) :
    (u.ofLp ⬝ᵥ u.ofLp) * (v.ofLp ⬝ᵥ v.ofLp) - (u.ofLp ⬝ᵥ v.ofLp) ^ 2 ≠ 0 := by
  have huu : (u.ofLp ⬝ᵥ u.ofLp) = 1 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : (v.ofLp ⬝ᵥ v.ofLp) = 1 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq, hv]; norm_num
  rw [huu, hvv, one_mul]
  intro hcon
  set c : ℝ := (inner ℝ u v : ℝ) with hc
  have hcd : c = u.ofLp ⬝ᵥ v.ofLp := inner_eq_dotProduct u v
  have hc2 : c ^ 2 = 1 := by rw [hcd]; linarith
  have hzero : ‖u - c • v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, hu, hv, mul_one, one_pow]
    rw [← hc]
    nlinarith [hc2, sq_abs c]
  have hueq : u = c • v := by
    have hn : ‖u - c • v‖ = 0 := by nlinarith [norm_nonneg (u - c • v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hfac : (c - 1) * (c + 1) = 0 := by nlinarith [hc2]
  rcases mul_eq_zero.mp hfac with h | h
  · exact h1 (by rw [hueq, show c = 1 by linarith, one_smul])
  · exact h2 (by rw [hueq, show c = -1 by linarith]; module)

/-! ### The unit sphere -/

/-- The unit sphere of `ℝ³`. -/
