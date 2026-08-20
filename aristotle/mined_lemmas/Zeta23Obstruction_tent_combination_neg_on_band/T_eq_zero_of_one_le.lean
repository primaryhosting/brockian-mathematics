/-
# Tent Combination Neg On Band
Category: Brockian Corpus
Target: Zeta23Obstruction.tent_combination_neg_on_band
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Zeta23Obstruction

/-- The Fourier tent profile `T(a) = max 0 (1 - |a|)`. -/

lemma T_eq_zero_of_one_le {a : ℝ} (ha : 1 ≤ a) : T a = 0 := by
  have : |a| = a := abs_of_nonneg (le_trans zero_le_one ha)
  simp [T, this]
  linarith

/-- On `(1, 5/2)` the shifted tent is strictly positive. -/
