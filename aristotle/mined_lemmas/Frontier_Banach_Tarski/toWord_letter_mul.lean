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

theorem toWord_letter_mul (x : α × Bool) (w : FreeGroup α) :
    (FreeGroup.mk [x] * w).toWord =
      if w.toWord.head? = some (x.1, !x.2) then w.toWord.tail else x :: w.toWord := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton,
    List.singleton_append]
  exact reduce_cons_of_isReduced FreeGroup.isReduced_toWord

omit [DecidableEq α] in
/-- In a reduced word, the letter following `x` is never the inverse of `x`. -/
