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

theorem bsearch_isSome_iff (a : Array α) (k : α)
    (hlin : IsLinear α) (hsort : Sorted a) (lo hi : Nat) (hhi : hi ≤ a.size) :
    (bsearch a k lo hi).isSome ↔ ∃ i : Nat, lo ≤ i ∧ i < hi ∧ a[i]! = k :=
  bsearch_isSome_iff_aux a k hlin hsort (hi - lo) lo hi (Nat.le_refl _) hhi

/-- **Binary search is correct**: on a sorted array, binary search returns an
index if and only if the key is present in the array. -/
