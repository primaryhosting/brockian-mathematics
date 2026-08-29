import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the reductions of the
elements of `H` modulo `p` do not cover all residue classes mod `p`.  This is exactly the
condition under which the singular series of the tuple `H` is nonzero. -/

theorem localFactor_pos {H : Finset ℤ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p := by
  have hnu : nu H p < p := (admissible_iff_nu_lt H).1 hH p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < p := by linarith
  have hnum : 0 < 1 - (nu H p : ℝ) / p := by
    have : (nu H p : ℝ) < p := by exact_mod_cast hnu
    have := (div_lt_one hppos).2 this
    linarith
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hppos]; linarith
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- The gap tuple based at `7280`: the shift by `7280` of the admissible pattern
`{0, 2, 6, 8, 12}`. -/
