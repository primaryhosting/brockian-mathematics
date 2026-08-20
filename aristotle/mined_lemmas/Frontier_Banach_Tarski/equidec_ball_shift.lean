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

theorem equidec_ball_shift :
    BT.Equidec (BT.E ≃ᵢ BT.E) (closedBall (0 : BT.E) 1) (closedBall ballShift 1) := by
  have h := BT.Equidec.smul_set (IsometryEquiv.addRight ballShift) (closedBall (0 : BT.E) 1)
  have himg : (IsometryEquiv.addRight ballShift) • (closedBall (0 : BT.E) 1)
      = closedBall ballShift 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      show ‖x + ballShift - ballShift‖ ≤ 1
      simpa using hx
    · intro hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      refine ⟨y - ballShift, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hy
      · show y - ballShift + ballShift = y
        abel
  rwa [himg] at h

/-- **The Banach-Tarski paradox.**  The closed unit ball of `ℝ³` can be partitioned into
finitely many pieces which, after moving each piece by an isometry of `ℝ³`, form a partition
of two disjoint copies of the closed unit ball. -/
