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

@[simp] theorem mem_Wstart {w : FreeGroup (Fin 2)} {x : Fin 2 × Bool} :
    w ∈ Wstart x ↔ w.toWord.head? = some x := Iff.rfl

