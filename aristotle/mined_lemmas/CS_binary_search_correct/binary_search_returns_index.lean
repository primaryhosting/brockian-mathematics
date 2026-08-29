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

theorem binary_search_returns_index (a : Array α) (k : α) (hlin : IsLinear α)
    (i : Nat) (hres : binarySearch a k = some i) :
    ∃ h : i < a.size, a[i] = k := by
  have h := bsearch_sound a k hlin 0 a.size i hres
  exact ⟨h.2.1, by rw [← getElem!_pos a i h.2.1]; exact h.2.2⟩

/-- `Nat` (with its usual `<`) satisfies the trichotomy hypothesis, so the
correctness theorem applies to arrays of natural numbers. -/
