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

@[simp] theorem rotZlin_apply (c s : ℝ) (x : E) :
    rotZlin c s x = !₂[c * x 0 - s * x 1, s * x 0 + c * x 1, x 2] := rfl

