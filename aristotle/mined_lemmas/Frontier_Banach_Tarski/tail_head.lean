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

theorem tail_head?_ne {w : FreeGroup (Fin 2)} {x : Fin 2 × Bool}
    (hx : w.toWord.head? = some x) : w.toWord.tail.head? ≠ some (x.1, !x.2) := by
  have hred : FreeGroup.IsReduced w.toWord := FreeGroup.isReduced_toWord
  cases hw : w.toWord with
  | nil => rw [hw] at hx; simp at hx
  | cons hd tl =>
    rw [hw] at hx hred
    have hhd : hd = x := by simpa using hx
    subst hhd
    simp only [List.tail_cons]
    exact head?_tail_ne hred

