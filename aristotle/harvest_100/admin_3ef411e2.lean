/-
# Repaired Witness Neg At Deep Point
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repaired Witness Neg At Deep Point
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
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

/-- `cosh (6π) > 10`, via `cosh x ≥ exp x / 2` and `exp (6π) ≥ exp 18 ≥ (exp 9)^2 ≥ 100`. -/
lemma ten_lt_cosh_six_pi : 10 < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h18 : (18 : ℝ) < 6 * Real.pi := by linarith
  have hexp9 : (10 : ℝ) ≤ Real.exp 9 := by
    have h : (9 : ℝ) + 1 ≤ Real.exp 9 := Real.add_one_le_exp 9
    linarith
  have hexp18 : (100 : ℝ) ≤ Real.exp 18 := by
    have : Real.exp 18 = Real.exp 9 * Real.exp 9 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (9 : ℝ)]
  have hmono : Real.exp 18 ≤ Real.exp (6 * Real.pi) := Real.exp_le_exp.mpr h18.le
  have hneg : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  rw [Real.cosh_eq]
  linarith

theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by
    have hs : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos_iff.mpr (by linarith)
    have : 0 < Real.sinh (2 * Real.pi) / (2 * Real.pi) := div_pos hs (by linarith)
    positivity
  have hbr : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := ten_lt_cosh_six_pi
    linarith
  exact mul_neg_of_pos_of_neg hsq hbr

end Zeta23Obstruction


