/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, in front of the first element `b` of `l` with `r a b`. -/

theorem mem_orderedInsert {a b : α} {l : List α} :
    b ∈ orderedInsert r a l ↔ b = a ∨ b ∈ l :=
  (perm_orderedInsert r a l).mem_iff.trans List.mem_cons

