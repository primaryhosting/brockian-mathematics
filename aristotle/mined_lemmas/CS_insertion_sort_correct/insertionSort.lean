/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace CS

/-- `orderedInsert r a l` inserts `a` into `l` in front of the first element
`b` of `l` with `r a b`. -/

def insertionSort {α : Type u} (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | a :: l => orderedInsert r a (insertionSort r l)

/-- A list is sorted for `r` when every element is related to all later ones. -/
abbrev Sorted {α : Type u} (r : α → α → Prop) (l : List α) : Prop := List.Pairwise r l

section

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

@[simp]
