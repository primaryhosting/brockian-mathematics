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

theorem centerRot_pow_apply_zero (n : ℕ) :
    (centerRot ^ n) • (0 : E) = cVec - (rZ (n : ℝ)) • cVec := by
  have hneg : (rZ (n : ℝ)) • (-cVec : E) = -((rZ (n : ℝ)) • cVec) := by
    have h := so3_smul_sub (rZ (n : ℝ)) 0 cVec
    rw [zero_sub, so3_smul_zero, zero_sub] at h
    exact h
  rw [centerRot_pow_apply, zero_sub, hneg]
  abel

