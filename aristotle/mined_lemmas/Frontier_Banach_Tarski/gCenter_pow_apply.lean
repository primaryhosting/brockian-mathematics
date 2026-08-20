import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem gCenter_pow_apply (n : ℕ) : (gCenter ^ n) 0 =
    pHalf - (rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) pHalf := by
  have hconj : gCenter ^ n = IsometryEquiv.addRight pHalf *
      (toIso (rotZ (Real.cos 1) (Real.sin 1) cos_one_sin_one)) ^ n *
      (IsometryEquiv.addRight pHalf)⁻¹ := by
    induction n with
    | zero => simp [gCenter]
    | succ n ih =>
      rw [pow_succ, ih, gCenter, pow_succ]
      group
  rw [hconj]
  show (IsometryEquiv.addRight pHalf)
    (((toIso (rotZ (Real.cos 1) (Real.sin 1) cos_one_sin_one)) ^ n)
      ((IsometryEquiv.addRight pHalf)⁻¹ 0)) = _
  rw [addRight_inv_apply]
  rw [← map_pow toIso, rotZ_pow 1 n cos_one_sin_one (Real.cos_sq_add_sin_sq _)]
  show ((rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) (0 - pHalf))
      + pHalf = _
  rw [zero_sub, map_neg]
  abel

