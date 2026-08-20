/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series `𝔖(H)` of the tuple `H` is nonzero. -/

theorem singularFactor_pos (H : Finset ℤ) (hH : Admissible H) (p : ℕ) (hp : p.Prime) :
    0 < singularFactor H p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlt : (resCount H p : ℝ) < (p : ℝ) := by
    exact_mod_cast (admissible_iff_resCount_lt H).mp hH p hp
  have hnum : 0 < 1 - (resCount H p : ℝ) / (p : ℝ) := by
    have : (resCount H p : ℝ) / (p : ℝ) < 1 := (div_lt_one hp0).mpr hlt
    linarith
  have hden : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- A tuple with fewer than `p` elements always misses a residue class modulo `p`. -/
