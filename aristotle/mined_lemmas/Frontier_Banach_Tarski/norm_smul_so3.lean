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

theorem norm_smul_so3 (M : SO3) (x : E) : ‖M • x‖ = ‖x‖ := by
  have h := inner_smul_smul M x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (M • x), norm_nonneg x]

/-! ### Nonidentity rotations have few fixed points -/

