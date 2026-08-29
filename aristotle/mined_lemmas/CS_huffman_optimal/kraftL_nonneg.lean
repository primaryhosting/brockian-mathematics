import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem kraftL_nonneg (L : Multiset ℕ) : 0 ≤ kraftL L := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨k, _, rfl⟩ := hx
  positivity

/-- Writing the Kraft sum with a common denominator `2 ^ n`. -/
