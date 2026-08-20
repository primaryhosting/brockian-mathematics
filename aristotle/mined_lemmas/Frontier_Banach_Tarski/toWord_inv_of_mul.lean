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

theorem toWord_inv_of_mul (i : Fin 2) (w : FreeGroup (Fin 2)) :
    ((FreeGroup.of i)⁻¹ * w).toWord =
      if w.toWord.head? = some (i, true) then w.toWord.tail else (i, false) :: w.toWord := by
  rw [inv_of_eq_mk, toWord_letter_mul]
  simp

