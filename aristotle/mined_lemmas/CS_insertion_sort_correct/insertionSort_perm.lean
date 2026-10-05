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

theorem insertionSort_perm : ∀ l : List α, (insertionSort r l).Perm l
  | [] => List.Perm.refl _
  | a :: l => by
      rw [insertionSort_cons]
      exact (orderedInsert_perm r a (insertionSort r l)).trans ((insertionSort_perm l).cons a)

/-- `insertionSort` returns a sorted list, provided `r` is total and transitive. -/
