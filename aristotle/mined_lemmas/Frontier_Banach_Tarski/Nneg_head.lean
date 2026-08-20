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

theorem Nneg_head? {w : FreeGroup (Fin 2)} (hw : w ∈ Nneg) :
    w.toWord = [] ∨ w.toWord.head? = some ((0 : Fin 2), false) := by
  obtain ⟨n, hn⟩ := hw
  cases n with
  | zero => exact Or.inl (by simpa using hn)
  | succ m => exact Or.inr (by rw [hn]; simp [List.replicate_succ])

