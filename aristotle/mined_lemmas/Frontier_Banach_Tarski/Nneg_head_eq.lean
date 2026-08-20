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

theorem Nneg_head_eq {w : FreeGroup (Fin 2)} (hw : w ∈ Nneg) {x : Fin 2 × Bool}
    (hx : w.toWord.head? = some x) : x = ((0 : Fin 2), false) := by
  rcases Nneg_head? hw with h | h
  · rw [h] at hx; simp at hx
  · rw [h] at hx; simpa using hx.symm

