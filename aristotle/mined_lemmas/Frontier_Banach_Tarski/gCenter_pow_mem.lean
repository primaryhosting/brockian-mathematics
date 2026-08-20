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

theorem gCenter_pow_mem (n : ℕ) : (gCenter ^ n) 0 ∈ closedBall (0 : E) 1 := by
  rw [gCenter_pow_apply n]
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖pHalf - (rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) pHalf‖
      ≤ ‖pHalf‖ + ‖(rotZ (Real.cos (n * 1)) (Real.sin (n * 1))
        (Real.cos_sq_add_sin_sq _)) pHalf‖ := norm_sub_le _ _
    _ = 1 := by rw [LinearIsometryEquiv.norm_map, norm_pHalf]; norm_num

/-- The closed unit ball is equidecomposable with the punctured closed unit ball. -/
