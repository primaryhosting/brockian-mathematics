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

@[simp] theorem evalW_cons (x : Fin 2 × Bool) (L : List (Fin 2 × Bool)) :
    evalW (x :: L) = stp x (evalW L) := rfl

/-- If the first letter of `L` is of type `b`, then the first coordinate is divisible by 3. -/
