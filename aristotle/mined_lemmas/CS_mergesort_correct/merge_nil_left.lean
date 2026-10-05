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

@[simp] theorem merge_nil_left (le : α → α → Bool) (ys : List α) : merge le [] ys = ys := by
  cases ys <;> simp [merge]

