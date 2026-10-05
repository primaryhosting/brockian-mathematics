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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- `cosh (6π) > 10`, via `cosh x ≥ exp x / 2`, `6π ≥ 18` and `exp 18 = (exp 3)^6 ≥ 4^6`. -/
theorem ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h18 : (18 : ℝ) ≤ 6 * Real.pi := by linarith
  have h3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have hpow : (4 : ℝ) ^ 6 ≤ (Real.exp 3) ^ 6 := by gcongr
  have he18 : (4096 : ℝ) ≤ Real.exp 18 := by
    have h : (Real.exp 3) ^ 6 = Real.exp 18 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [← h]; linarith [hpow]
  have hmono : Real.exp 18 ≤ Real.exp (6 * Real.pi) := Real.exp_le_exp.2 h18
  have hcosh : Real.cosh (6 * Real.pi)
      = (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := Real.cosh_eq _
  have hpos : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  rw [hcosh]; linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`:
`(sinh 2π / 2π)^2 * (1 - cosh(6π)/10) < 0`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2
      * (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : 0 < Real.sinh (2 * Real.pi) := by
    rw [Real.sinh_eq]
    have := Real.exp_lt_exp.2 (show -(2 * Real.pi) < 2 * Real.pi by linarith)
    linarith
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by positivity
  have hb : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := ten_lt_cosh_six_pi; linarith
  exact mul_neg_of_pos_of_neg hsq hb

end Zeta23Obstruction

