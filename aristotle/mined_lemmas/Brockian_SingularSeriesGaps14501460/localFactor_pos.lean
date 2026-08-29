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

lemma localFactor_pos {p : ℕ} (hp : p.Prime) : 0 < localFactor gapTuple p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnu : (nu gapTuple p : ℝ) < (p : ℝ) := by exact_mod_cast nu_gapTuple_lt hp
  have h1 : 0 < 1 - (nu gapTuple p : ℝ) / p := by
    rw [sub_pos, div_lt_one hp0]; exact hnu
  exact div_pos h1 (pow_pos (one_sub_inv_pos hp) _)

