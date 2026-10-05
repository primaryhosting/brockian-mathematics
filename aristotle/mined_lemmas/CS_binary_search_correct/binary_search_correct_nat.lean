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

theorem binary_search_correct_nat (a : Array Nat) (k : Nat) (hsort : Sorted a) :
    (binarySearch a k).isSome ↔ ∃ i : Nat, ∃ h : i < a.size, a[i] = k :=
  binary_search_correct a k isLinear_nat hsort

end CS

import RequestProject.Main
import Mathlib

/-!
# Binary search correctness for an arbitrary `LinearOrder` (Mathlib version)

The core development in `RequestProject.Main` is stated for a type with a
decidable `<` satisfying trichotomy (`CS.IsLinear`).  Here we specialise it to
Mathlib's `LinearOrder`, where the hypotheses are automatic and sortedness can
be phrased with `≤`.
-/

namespace CS

variable {α : Type*} [LinearOrder α] [Inhabited α]

omit [Inhabited α] in
