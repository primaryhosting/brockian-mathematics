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

def Nneg₁ : Set (FreeGroup (Fin 2)) :=
  {w | ∃ n : ℕ, 0 < n ∧ w.toWord = List.replicate n ((0 : Fin 2), false)}

