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

def orderedInsert {α : Type u} (r : α → α → Prop) [DecidableRel r] (a : α) :
    List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedInsert r a l

/-- Insertion sort with respect to the relation `r`. -/
