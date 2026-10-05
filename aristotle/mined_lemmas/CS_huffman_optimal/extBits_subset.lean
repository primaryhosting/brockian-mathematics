import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem extBits_subset {s : List Bool} {k m : ℕ} (h : s.length + k = m) :
    extBits s k ⊆ allBits m := by
  intro l hl
  simp only [extBits, Finset.mem_image, mem_allBits] at hl
  obtain ⟨t, ht, rfl⟩ := hl
  simp [← h, ht]

