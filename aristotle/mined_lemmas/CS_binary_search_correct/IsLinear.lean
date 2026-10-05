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

def IsLinear (α : Type u) [LT α] : Prop :=
  ∀ x y : α, ¬ (x < y) → ¬ (y < x) → x = y

/-- Binary search for the key `k` in the slice `[lo, hi)` of the array `a`.
Returns `some i` for an index `i` holding `k`, and `none` when `k` does not
occur in that slice. -/
