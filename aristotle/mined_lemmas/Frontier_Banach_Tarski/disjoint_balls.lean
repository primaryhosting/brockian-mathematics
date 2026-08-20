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

theorem disjoint_balls :
    Disjoint (closedBall (0 : BT.E) 1) (closedBall ballShift 1) := by
  refine Set.disjoint_left.2 ?_
  intro y hy hy'
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  rw [Metric.mem_closedBall, dist_eq_norm] at hy'
  have h3 : ‖ballShift‖ ≤ ‖y‖ + ‖y - ballShift‖ := by
    calc ‖ballShift‖ = ‖y - (y - ballShift)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖y - ballShift‖ := norm_sub_le _ _
  rw [norm_ballShift] at h3
  linarith

