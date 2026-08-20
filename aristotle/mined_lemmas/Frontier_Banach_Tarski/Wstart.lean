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

def Wstart (x : Fin 2 × Bool) : Set (FreeGroup (Fin 2)) :=
  {w | w.toWord.head? = some x}

/-- The set of nonpositive powers of the first generator, i.e. words of the form `a⁻ⁿ`. -/
