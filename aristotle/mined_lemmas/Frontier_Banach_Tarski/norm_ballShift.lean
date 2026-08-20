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

theorem norm_ballShift : ‖ballShift‖ = 3 := by
  rw [EuclideanSpace.norm_eq]
  simp [ballShift, Fin.sum_univ_three]

