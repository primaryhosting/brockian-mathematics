import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma sum_inv_sq_le' : ∀ B : ℕ, 1 ≤ B → ∑ b ∈ Icc 1 B, (1 / (b : ℝ) ^ 2) ≤ 2 - 1 / B := by
  intro B hB
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ B hB ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hB0 : (0:ℝ) < B := by exact_mod_cast hB
    have key : 1 / ((B : ℝ) + 1) ^ 2 ≤ 1 / B - 1 / ((B : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff (by positivity)
        (by positivity)]
      ring_nf
      nlinarith
    push_cast
    linarith

