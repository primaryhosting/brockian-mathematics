/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

universe u

variable {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] [Inhabited α]

/-- `Sorted a` says that the array `a` is weakly increasing: no later entry is
strictly smaller than an earlier one. -/

theorem sorted_of_monotone {a : Array α}
    (h : ∀ i j : ℕ, i ≤ j → j < a.size → a[i]! ≤ a[j]!) : Sorted a :=
  fun i j hij hj => not_lt.mpr (h i j hij hj)

/-- **Binary search is correct** over an arbitrary linear order: on a sorted
array, binary search returns an index iff the key is present. -/
