/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u}

/-- Split a list into two lists by alternately distributing its elements. -/

theorem mergesort_cons_cons (le : α → α → Bool) (a b : α) (l : List α) :
    mergesort le (a :: b :: l) =
      merge le (mergesort le (a :: (split l).1)) (mergesort le (b :: (split l).2)) := by
  rw [mergesort]

