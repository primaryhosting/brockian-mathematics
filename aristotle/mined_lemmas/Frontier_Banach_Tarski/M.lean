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

def M : Set E := Set.range fun q : Quotient orbitSetoid => ((Quotient.out q : ↥SX) : E)

