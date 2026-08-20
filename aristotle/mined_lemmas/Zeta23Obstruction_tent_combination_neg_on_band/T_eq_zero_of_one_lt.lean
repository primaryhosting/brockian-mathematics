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

/-- The tent profile `T a = max 0 (1 - |a|)`. -/

lemma T_eq_zero_of_one_lt {a : ℝ} (ha : 1 < a) : T a = 0 := by
  have h : |a| = a := abs_of_pos (lt_trans one_pos ha)
  simp only [T, h]
  exact max_eq_left (by linarith)

/-- On the band `(1, 5/2)`, the shifted tent `T (a - 3/2)` is strictly positive. -/
