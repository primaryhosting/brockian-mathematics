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

lemma one_sub_le_localFactor {p : ℕ} (hp : 11 ≤ p) :
    1 - 9 / (p : ℝ) ^ 2 ≤ localFactor gapTuple p := by
  have ht : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have ht0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one ht0]; linarith
  rw [localFactor, gapTuple_card, nu_gapTuple_eq_four (by omega), le_div_iff₀ (pow_pos hpos 4)]
  have hkey : (1 - 4 / (p : ℝ)) - (1 - 9 / (p : ℝ) ^ 2) * (1 - 1 / (p : ℝ)) ^ 4
      = (3 * (p : ℝ) ^ 4 - 32 * (p : ℝ) ^ 3 + 53 * (p : ℝ) ^ 2 - 36 * (p : ℝ) + 9)
        / (p : ℝ) ^ 6 := by
    field_simp
    ring
  have hnum : (0:ℝ) ≤ 3 * (p : ℝ) ^ 4 - 32 * (p : ℝ) ^ 3 + 53 * (p : ℝ) ^ 2 - 36 * (p : ℝ) + 9 := by
    nlinarith [ht, ht0, sq_nonneg ((p:ℝ) - 11), pow_pos ht0 3, pow_pos ht0 2]
  nlinarith [hkey, div_nonneg hnum (by positivity : (0:ℝ) ≤ (p : ℝ) ^ 6)]

/-! ## Weierstrass product inequality and the tail bound -/

