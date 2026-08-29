/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- `residueCount H p` is the number of distinct residue classes modulo `p`
occupied by the shifts in the tuple `H`. -/

theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : 0 < 1 - (residueCount H p : ℝ) / p := by
    have : (residueCount H p : ℝ) < p := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).2 this
    linarith
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]; linarith
    linarith
  exact mul_pos h1 (zpow_pos h2 _)

/-- The `n`-term *gap ladder*: the shifts `0, n!, 2·n!, …, (n-1)·n!`. -/
