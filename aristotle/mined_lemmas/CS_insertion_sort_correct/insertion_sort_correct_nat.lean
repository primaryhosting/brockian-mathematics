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

theorem insertion_sort_correct_nat (l : List Nat) :
    Sorted (· ≤ ·) (insertionSort (· ≤ ·) l) ∧ (insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct (· ≤ ·) (fun x y => Nat.le_total x y)
    (fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂) l

end CS

