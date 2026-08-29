/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This module is deliberately import-free (Lean's `Init` prelude only), because a
module doc comment such as the header above must be the very first command in a
file and therefore cannot be preceded by `import` lines.  Everything used below
(`List.Perm`, `List.Pairwise`, `DecidableRel`) is part of the Lean 4 core
library, and `List.Pairwise r` is by definition Mathlib's `List.Sorted r`.
The Mathlib-facing corollaries (`List.Sorted (· ≤ ·)` for a `LinearOrder`, and
agreement with `List.insertionSort`) live in `RequestProject.Main`.
-/

namespace CS

universe u

variable {α : Type u}

section

variable (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, in front of the first element `b` with `r a b`. -/

theorem insertionSort_sorted_perm [LinearOrder α] (l : List α) :
    List.Pairwise (fun x y : α => x ≤ y) (CS.insertionSort (fun x y : α => x ≤ y) l) ∧
      (CS.insertionSort (fun x y : α => x ≤ y) l).Perm l :=
  CS.insertion_sort_correct (r := fun x y : α => x ≤ y)
    (fun _ _ _ h₁ h₂ => le_trans h₁ h₂) (fun x y => le_total x y) l

end CS

#print axioms CS.insertion_sort_correct
#print axioms CS.insertionSort_eq
#print axioms CS.insertionSort_sorted_perm

