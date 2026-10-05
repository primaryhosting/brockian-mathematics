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

theorem insertion_sort_correct (htotal : ∀ x y : α, r x y ∨ r y x)
    (htrans : ∀ x y z : α, r x y → r y z → r x z) (l : List α) :
    Sorted r (insertionSort r l) ∧ (insertionSort r l).Perm l :=
  ⟨sorted_insertionSort r htotal htrans l, insertionSort_perm r l⟩

end

/-- Specialization to `≤` on the natural numbers. -/
