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

/-- The unit tent profile `T a = max 0 (1 - |a|)`. -/

lemma T_pos_of_abs_lt_one {a : ℝ} (ha : |a| < 1) : 0 < T a := by
  have : 0 < 1 - |a| := by linarith
  exact lt_max_of_lt_right this

/--
The Fourier tent combination `T α - (1/20)(T (α - 3/2) + T (α + 3/2))` is strictly
negative on the band `1 < α < 5/2`.
-/
