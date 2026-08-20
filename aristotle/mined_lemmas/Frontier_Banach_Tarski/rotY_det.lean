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

theorem rotY_det (t : ℝ) : (rotY t).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [rotY]
  nlinarith [Real.sin_sq_add_cos_sq t]

