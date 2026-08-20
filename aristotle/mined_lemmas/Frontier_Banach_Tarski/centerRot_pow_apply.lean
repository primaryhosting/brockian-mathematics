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

theorem centerRot_pow_apply (n : ℕ) : ∀ x : E,
    (centerRot ^ n) • x = cVec + (rZ (n : ℝ)) • (x - cVec) := by
  induction n with
  | zero =>
      intro x
      simp only [pow_zero, Nat.cast_zero, rZ_zero, one_smul]
      abel
  | succ m ih =>
      intro x
      rw [pow_succ, SemigroupAction.mul_smul, ih, centerRot_apply,
        show (cVec + rZ 1 • (x - cVec) - cVec : E) = rZ 1 • (x - cVec) by abel,
        Nat.cast_add, Nat.cast_one, rZ_add, ← smul_smul]

