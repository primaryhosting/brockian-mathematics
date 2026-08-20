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

theorem head?_cases (w : FreeGroup (Fin 2)) :
    w.toWord = [] ∨ ∃ x : Fin 2 × Bool, w.toWord.head? = some x := by
  cases h : w.toWord with
  | nil => exact Or.inl rfl
  | cons hd tl => exact Or.inr ⟨hd, by simp⟩

