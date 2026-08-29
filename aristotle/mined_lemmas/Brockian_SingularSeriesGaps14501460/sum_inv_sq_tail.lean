import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma sum_inv_sq_tail (M : ℕ) : ∑ n ∈ Finset.Ico 11 M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 10 := by
  by_cases hM : M ≤ 11
  · rw [Finset.Ico_eq_empty (by omega)]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, M = 11 + k := ⟨M - 11, by omega⟩
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpos : (0 : ℝ) < 1 / (10 + (k : ℝ)) := by positivity
    linarith [sum_inv_sq_aux k]

