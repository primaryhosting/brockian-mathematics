/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

theorem singularFactor_pos {H : Finset ℤ} (hH : IsAdmissible H) {p : ℕ} (hp : p.Prime) :
    0 < singularFactor p H := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hnum : 0 < 1 - (nu p H : ℝ) / p := by
    have : (nu p H : ℝ) < p := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).2 this
    linarith
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- Every partial singular series of an admissible tuple is positive. -/
