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

def piece : Fin 4 → Set (FreeGroup (Fin 2))
  | 0 => Wstart (0, true) ∪ Nneg
  | 1 => Wstart (0, false) \ Nneg₁
  | 2 => Wstart (1, true)
  | 3 => Wstart (1, false)

