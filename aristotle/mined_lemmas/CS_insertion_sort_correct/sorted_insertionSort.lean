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

theorem sorted_insertionSort (htotal : ∀ x y : α, r x y ∨ r y x)
    (htrans : ∀ x y z : α, r x y → r y z → r x z) :
    ∀ l : List α, Sorted r (insertionSort r l)
  | [] => List.Pairwise.nil
  | a :: l => sorted_orderedInsert r htotal htrans a _ (sorted_insertionSort htotal htrans l)

/-- **Insertion sort is correct**: for a total, transitive relation `r`,
`insertionSort r l` is a sorted permutation of `l`. -/
