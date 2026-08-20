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

noncomputable def v0 : E := !₂[0, 1, 0]

/-- The image of `v₀` under the rotation attached to a word, in terms of the integer
recursion. -/
