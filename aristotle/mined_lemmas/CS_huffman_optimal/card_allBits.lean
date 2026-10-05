import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem card_allBits (n : ℕ) : (allBits n).card = 2 ^ n := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
      have hdisj : Disjoint ((allBits n).image (fun l => false :: l))
          ((allBits n).image (fun l => true :: l)) := by
        rw [Finset.disjoint_left]
        rintro l hl hl'
        simp only [Finset.mem_image] at hl hl'
        obtain ⟨x, _, rfl⟩ := hl
        obtain ⟨y, _, hy⟩ := hl'
        exact absurd hy (by simp)
      rw [allBits, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun x y h => by simpa using h),
        Finset.card_image_of_injective _ (fun x y h => by simpa using h), ih]
      ring

/-- All extensions of `s` by `k` bits. -/
