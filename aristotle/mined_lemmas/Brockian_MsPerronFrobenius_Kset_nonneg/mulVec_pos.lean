import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma mulVec_pos (hpos : ∀ i j, 0 < M i j) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hx0 : x ≠ 0) (i : Fin n) : 0 < M.mulVec x i := by
  -- Since x ≠ 0 and all x i ≥ 0, there exists some k with x k > 0
  obtain ⟨k, hk⟩ : ∃ k, 0 < x k := by
    by_contra h
    push_neg at h
    exact hx0 (funext fun j => le_antisymm (h j) (hx j))
  -- Since M i k > 0 and x k > 0, we have M i k * x k > 0
  have hterm : 0 < M i k * x k := mul_pos (hpos i k) hk
  -- M.mulVec x i ≥ M i k * x k since it's a sum of nonneg terms
  have hge : M i k * x k ≤ M.mulVec x i := by
    simp [Matrix.mulVec]
    apply Finset.single_le_sum (fun j _ => mul_nonneg (le_of_lt (hpos i j)) (hx j))
    simp
  linarith

/-- Existence of a uniform lower bound `δ` for normalized images, and an entry bound `B`. -/
