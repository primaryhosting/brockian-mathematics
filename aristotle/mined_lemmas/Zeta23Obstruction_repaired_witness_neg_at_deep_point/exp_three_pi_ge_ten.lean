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

/-- `exp (3π) ≥ 10`, from `exp x ≥ x + 1` and `π > 3`. -/

lemma exp_three_pi_ge_ten : (10 : ℝ) ≤ Real.exp (3 * Real.pi) := by
  have h1 : (3 : ℝ) * Real.pi + 1 ≤ Real.exp (3 * Real.pi) := Real.add_one_le_exp _
  have h2 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  linarith

/-- `cosh (6π) > 10`. -/
