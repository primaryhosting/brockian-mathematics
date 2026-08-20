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

@[simp] theorem rotXlin_apply (c s : ℝ) (x : E) :
    rotXlin c s x = !₂[x 0, c * x 1 - s * x 2, s * x 1 + c * x 2] := rfl

/-- Rotation of `ℝ³` about the `z`-axis, with cosine `c` and sine `s`. -/
