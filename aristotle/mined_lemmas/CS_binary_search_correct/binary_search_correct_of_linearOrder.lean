/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u} [LT α] [DecidableLT α]

/-- Binary search for `key` in the index range `[lo, hi)` of the indexed collection `f`,
returning an index at which the key sits, if any. -/

theorem binary_search_correct_of_linearOrder {α : Type*} [LinearOrder α] [Inhabited α]
    (a : Array α) (key : α)
    (hsorted : ∀ i j : ℕ, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    (CS.binarySearch a key).isSome ↔ key ∈ a :=
  CS.binary_search_correct
    (fun _ _ hxy hyx => le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)) a key
    (fun i j hij hj => not_lt.mpr (hsorted i j hij hj))

end CS

-- Sanity checks.
example : CS.binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by
  simp [CS.binarySearch, CS.bsearchAux]
example : CS.binarySearch #[1, 3, 5, 7, 9] 4 = none := by
  simp [CS.binarySearch, CS.bsearchAux]

#print axioms CS.binary_search_correct

