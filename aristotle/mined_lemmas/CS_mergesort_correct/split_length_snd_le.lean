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

theorem split_length_snd_le (l : List α) : (split l).2.length ≤ l.length := (split_length l).2

/-- Merge two lists with respect to a boolean comparison `le`. -/
