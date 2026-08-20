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

def star (A : Set E) : Set E := {y : E | y ≠ 0 ∧ ‖y‖ ≤ 1 ∧ ‖y‖⁻¹ • y ∈ A}

