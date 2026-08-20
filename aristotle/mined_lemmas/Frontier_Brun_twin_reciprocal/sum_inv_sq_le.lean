import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma sum_inv_sq_le (B : ℕ) : ∑ b ∈ Icc 1 B, (1 / (b : ℝ) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  · have := sum_inv_sq_le' B hB
    have : (0:ℝ) < B := by exact_mod_cast hB
    have h2 := sum_inv_sq_le' B hB
    have : (0:ℝ) ≤ 1 / B := by positivity
    linarith

/-- Squarefree numbers in `[1, z]`. -/
