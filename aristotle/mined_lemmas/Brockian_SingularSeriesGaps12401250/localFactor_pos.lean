/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Key Mathlib ingredients used: `Finset.card_image_le` (a tuple occupies at most `#H`
residue classes, so only primes `p ≤ #H` can obstruct admissibility),
`ZMod.intCast_zmod_eq_zero_iff_dvd` and `even_iff_two_dvd` (the prime `2` analysis),
`Finset.prod_pos` and `zpow_pos` (positivity of the singular series).
-/

open Finset

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the integer tuple `H`. -/

theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : 0 < 1 - ((residues H p).card : ℝ) / (p : ℝ) := by
    have hlt : ((residues H p).card : ℝ) < (p : ℝ) := by exact_mod_cast hH p hp
    have : ((residues H p).card : ℝ) / (p : ℝ) < 1 := (div_lt_one hp0).2 hlt
    linarith
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-- The partial singular series of an admissible tuple is strictly positive. -/
