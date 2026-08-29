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

lemma sum_inv_sq_aux (k : ℕ) :
    ∑ n ∈ Finset.Ico 11 (11 + k), (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 10 - 1 / (10 + (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : 11 ≤ 11 + k := by omega
    have hrw : 11 + (k + 1) = (11 + k) + 1 := by omega
    rw [hrw, Finset.sum_Ico_succ_top hle]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcast : ((11 + k : ℕ) : ℝ) = 11 + (k : ℝ) := by push_cast; ring
    rw [hcast]
    have hstep : (1 : ℝ) / (11 + (k : ℝ)) ^ 2
        ≤ 1 / (10 + (k : ℝ)) - 1 / (10 + ((k : ℝ) + 1)) := by
      have h1 : (0 : ℝ) < 10 + (k : ℝ) := by linarith
      have h2 : (0 : ℝ) < 11 + (k : ℝ) := by linarith
      have e : 1 / (10 + (k : ℝ)) - 1 / (10 + ((k : ℝ) + 1))
          = 1 / ((10 + (k : ℝ)) * (11 + (k : ℝ))) := by
        field_simp
        ring
      rw [e]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hcast3 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast3]
    linarith [ih, hstep]

