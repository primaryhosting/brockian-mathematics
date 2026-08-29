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

theorem isLinear_nat : IsLinear Nat := by
  intro x y hxy hyx
  omega

/-- Concrete instance of the main theorem for `Array Nat`. -/
