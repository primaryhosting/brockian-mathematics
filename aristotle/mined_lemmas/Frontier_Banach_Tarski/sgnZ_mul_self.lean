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

theorem sgnZ_mul_self (b : Bool) : sgnZ b * sgnZ b = 1 := by cases b <;> simp [sgnZ]

/-- One step of the integer recursion, corresponding to applying one generator. -/
