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

/-- `exp 6 ≥ 7`, from `1 + x ≤ exp x`. -/

lemma seven_le_exp_six : (7 : ℝ) ≤ Real.exp 6 := by
  have h := Real.add_one_le_exp (6 : ℝ)
  linarith

/-- `cosh (6π) > 10`. -/
