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

theorem mem_piece_three {w : FreeGroup (Fin 2)} :
    w ∈ piece 3 ↔ w.toWord.head? = some ((1 : Fin 2), false) := Iff.rfl

