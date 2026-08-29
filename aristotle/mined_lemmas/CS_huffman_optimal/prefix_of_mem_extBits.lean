import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem prefix_of_mem_extBits {s l : List Bool} {k : ℕ} (h : l ∈ extBits s k) : s <+: l := by
  simp only [extBits, Finset.mem_image] at h
  obtain ⟨t, _, rfl⟩ := h
  exact ⟨t, rfl⟩

/-- **Kraft's inequality**: for a prefix-free code on a finite alphabet,
`∑ 2 ^ (-length)` is at most `1`. -/
