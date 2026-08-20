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

lemma twenty_lt_exp_six_pi : (20 : ℝ) < Real.exp (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h18 : (18 : ℝ) ≤ 6 * Real.pi := by linarith
  have hmono : Real.exp 18 ≤ Real.exp (6 * Real.pi) := Real.exp_le_exp.mpr h18
  have hsplit : Real.exp 18 = Real.exp 9 * Real.exp 9 := by
    rw [← Real.exp_add]; norm_num
  have h9 := ten_le_exp_nine
  nlinarith

/-- The deep-point value of `cosh` exceeds `10`. -/
