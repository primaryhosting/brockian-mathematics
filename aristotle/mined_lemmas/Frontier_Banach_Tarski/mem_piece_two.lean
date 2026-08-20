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

theorem mem_piece_two {w : FreeGroup (Fin 2)} :
    w ∈ piece 2 ↔ w.toWord.head? = some ((1 : Fin 2), true) := Iff.rfl

