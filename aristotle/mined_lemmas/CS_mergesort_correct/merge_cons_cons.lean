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

theorem merge_cons_cons (le : α → α → Bool) (x y : α) (xs ys : List α) :
    merge le (x :: xs) (y :: ys) =
      if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys := by
  rw [merge]

