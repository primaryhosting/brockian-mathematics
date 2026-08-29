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

theorem mem_orderedInsert {a b : α} {l : List α} :
    b ∈ orderedInsert r a l ↔ b = a ∨ b ∈ l := by
  have h := (orderedInsert_perm r a l).mem_iff (a := b)
  simpa using h

/-- Inserting into a sorted list keeps it sorted, provided `r` is total and transitive. -/
