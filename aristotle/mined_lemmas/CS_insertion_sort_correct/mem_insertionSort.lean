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

theorem mem_insertionSort {a : α} {l : List α} : a ∈ insertionSort r l ↔ a ∈ l :=
  (perm_insertionSort r l).mem_iff

section Total

variable (htotal : ∀ a b, r a b ∨ r b a) (htrans : ∀ {a b c}, r a b → r b c → r a c)

include htotal htrans in
/-- Inserting an element into a sorted list keeps it sorted. -/
