/-
# Repaired Witness Neg At Deep Point
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
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

set_option grind.warning false

namespace Zeta23Obstruction

/-- `exp 9 ≥ 10`, a crude bound from `1 + x ≤ exp x`. -/

lemma ten_le_exp_nine : (10 : ℝ) ≤ Real.exp 9 := by
  have h := Real.add_one_le_exp (9 : ℝ)
  linarith

/-- `exp (6π) > 20`. -/
