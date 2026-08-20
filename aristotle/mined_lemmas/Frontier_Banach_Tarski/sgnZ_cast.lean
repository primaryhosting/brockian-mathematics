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

@[simp] theorem sgnZ_cast (b : Bool) : ((sgnZ b : ℤ) : ℝ) = sgnR b := by
  cases b <;> simp [sgnZ, sgnR]

