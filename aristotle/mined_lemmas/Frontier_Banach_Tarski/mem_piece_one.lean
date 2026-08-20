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

theorem mem_piece_one {w : FreeGroup (Fin 2)} :
    w ∈ piece 1 ↔ (w.toWord.head? = some ((0 : Fin 2), false) ∧ w ∉ Nneg₁) := Iff.rfl

