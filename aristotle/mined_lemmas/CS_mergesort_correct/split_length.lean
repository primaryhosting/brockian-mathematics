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

theorem split_length (l : List α) :
    (split l).1.length ≤ l.length ∧ (split l).2.length ≤ l.length := by
  induction l with
  | nil => simp [split]
  | cons a l ih =>
      constructor
      · show (split l).2.length ≤ l.length + 1
        omega
      · show ((split l).1).length + 1 ≤ l.length + 1
        omega

