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

lemma inv_le_localFactor {p : ℕ} (hp : p.Prime) : 1 / (p : ℝ) ≤ localFactor gapTuple p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnu : (nu gapTuple p : ℝ) ≤ (p : ℝ) - 1 := by
    have := nu_gapTuple_lt hp
    have : (nu gapTuple p : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast this
    linarith
  have hA : 1 / (p : ℝ) ≤ 1 - (nu gapTuple p : ℝ) / p := by
    have key : (1 - (nu gapTuple p : ℝ) / p) - 1 / p
        = ((p : ℝ) - (nu gapTuple p : ℝ) - 1) / p := by
      field_simp
    have hnn : 0 ≤ ((p : ℝ) - (nu gapTuple p : ℝ) - 1) / p :=
      div_nonneg (by linarith) hp0.le
    linarith
  have hden : 0 < (1 - 1 / (p : ℝ)) ^ 4 := pow_pos (one_sub_inv_pos hp) _
  have hden1 : (1 - 1 / (p : ℝ)) ^ 4 ≤ 1 := by
    have h1 : 1 - 1 / (p : ℝ) ≤ 1 := by
      have : 0 < 1 / (p : ℝ) := by positivity
      linarith
    exact pow_le_one₀ (le_of_lt (one_sub_inv_pos hp)) h1
  rw [localFactor, gapTuple_card, le_div_iff₀ hden]
  nlinarith [hA, hden, hden1, one_div_pos.mpr hp0]

