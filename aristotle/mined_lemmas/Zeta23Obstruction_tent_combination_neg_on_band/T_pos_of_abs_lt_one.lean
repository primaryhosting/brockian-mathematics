import Mathlib

/-!
# Tent Combination Neg On Band
Category: Brockian Corpus
Target: Zeta23Obstruction.tent_combination_neg_on_band
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

namespace Zeta23Obstruction

/-- The Fourier tent profile `T a = max 0 (1 - |a|)`. -/

lemma T_pos_of_abs_lt_one {a : ℝ} (h : |a| < 1) : 0 < T a :=
  lt_max_of_lt_right (by linarith)

/-- On the band `(1, 5/2)`, the tent combination
`T a - (1/20) * (T (a - 3/2) + T (a + 3/2))` is strictly negative. -/
