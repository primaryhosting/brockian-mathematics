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

lemma tail_prod_ge (N : ℕ) :
    (1 : ℝ) / 10 ≤ ∏ p ∈ (Finset.Ico 11 (N + 1)).filter Nat.Prime, localFactor gapTuple p := by
  set s := (Finset.Ico 11 (N + 1)).filter Nat.Prime with hs
  have hmem : ∀ p ∈ s, 11 ≤ p := by
    intro p hp
    rw [hs, Finset.mem_filter, Finset.mem_Ico] at hp
    exact hp.1.1
  have hb : ∀ p ∈ s, (11 : ℝ) ≤ (p : ℝ) := fun p hp => by exact_mod_cast hmem p hp
  have h1 : ∏ p ∈ s, (1 - 9 / (p : ℝ) ^ 2) ≤ ∏ p ∈ s, localFactor gapTuple p := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have := hb p hp
      have : (9 : ℝ) / (p : ℝ) ^ 2 ≤ 9 / 121 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith [hb p hp]
      linarith
    · intro p hp
      exact one_sub_le_localFactor (hmem p hp)
  have h2 : 1 - ∑ p ∈ s, 9 / (p : ℝ) ^ 2 ≤ ∏ p ∈ s, (1 - 9 / (p : ℝ) ^ 2) := by
    refine prod_one_sub_ge s _ ?_ ?_
    · intro p hp
      have := hb p hp
      positivity
    · intro p hp
      have h := hb p hp
      rw [div_le_one (by nlinarith)]
      nlinarith
  have h3 : ∑ p ∈ s, 9 / (p : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Ico 11 (N + 1), 9 / (n : ℝ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro n _ _
    positivity
  have h4 : ∑ n ∈ Finset.Ico 11 (N + 1), (9 : ℝ) / (n : ℝ) ^ 2 ≤ 9 / 10 := by
    have : ∑ n ∈ Finset.Ico 11 (N + 1), (9 : ℝ) / (n : ℝ) ^ 2
        = 9 * ∑ n ∈ Finset.Ico 11 (N + 1), (1 : ℝ) / (n : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    linarith [sum_inv_sq_tail (N + 1)]
  linarith

/-! ## The partial products -/

