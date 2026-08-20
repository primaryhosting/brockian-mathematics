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

@[simp] theorem rotX_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (x : E) :
    rotX c s h x = !₂[x 0, c * x 1 - s * x 2, s * x 1 + c * x 2] := rfl

