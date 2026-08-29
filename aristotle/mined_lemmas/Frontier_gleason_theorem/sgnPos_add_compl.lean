import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

lemma sgnPos_add_compl (x y z : ℝ) (h : x = 1 / 2 → (y ≠ 0 ∨ z ≠ 0)) :
    (if sgnPos x y z then (1 : ℝ) else 0) + (if sgnPos (1 - x) (-y) (-z) then (1 : ℝ) else 0)
      = 1 := by
  unfold sgnPos
  rcases lt_trichotomy x (1 / 2) with hx | hx | hx
  · rw [if_neg (by rintro (h1 | ⟨h1, -⟩) <;> linarith), if_pos (by left; linarith)]
    norm_num
  · rcases h hx with hy | hz
    · rcases lt_or_gt_of_ne hy with hy' | hy'
      · rw [if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith),
          if_pos (by right; exact ⟨by linarith, Or.inl (by linarith)⟩)]
        norm_num
      · rw [if_pos (by right; exact ⟨hx, Or.inl hy'⟩),
          if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith)]
        norm_num
    · rcases em (y = 0) with hy0 | hy0
      · rcases lt_or_gt_of_ne hz with hz' | hz'
        · rw [if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, h3⟩)⟩) <;> linarith),
            if_pos (by right; exact ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩)]
          norm_num
        · rw [if_pos (by right; exact ⟨hx, Or.inr ⟨hy0, hz'⟩⟩),
            if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, h3⟩)⟩) <;> linarith)]
          norm_num
      · rcases lt_or_gt_of_ne hy0 with hy' | hy'
        · rw [if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith),
            if_pos (by right; exact ⟨by linarith, Or.inl (by linarith)⟩)]
          norm_num
        · rw [if_pos (by right; exact ⟨hx, Or.inl hy'⟩),
            if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith)]
          norm_num
  · rw [if_pos (by left; linarith), if_neg (by rintro (h1 | ⟨h1, -⟩) <;> linarith)]
    norm_num

/-- The two-valued "lexicographic" measure on `2 × 2` matrices. -/
