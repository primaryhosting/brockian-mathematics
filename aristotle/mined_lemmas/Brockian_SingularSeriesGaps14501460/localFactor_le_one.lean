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

lemma localFactor_le_one {p : ℕ} (hp : 11 ≤ p) : localFactor gapTuple p ≤ 1 := by
  have ht : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have ht0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one ht0]; linarith
  rw [localFactor, gapTuple_card, nu_gapTuple_eq_four (by omega), div_le_one (pow_pos hpos 4)]
  have hkey : (1 - 1 / (p : ℝ)) ^ 4 - (1 - 4 / (p : ℝ))
      = (6 * (p : ℝ) ^ 2 - 4 * (p : ℝ) + 1) / (p : ℝ) ^ 4 := by
    field_simp
    ring
  nlinarith [hkey, div_nonneg (by nlinarith : (0:ℝ) ≤ 6 * (p : ℝ) ^ 2 - 4 * (p : ℝ) + 1)
    (by positivity : (0:ℝ) ≤ (p : ℝ) ^ 4)]

