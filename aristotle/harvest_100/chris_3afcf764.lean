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
lemma twenty_lt_exp_six_pi : (20 : ℝ) < Real.exp (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h18 : (18 : ℝ) ≤ 6 * Real.pi := by linarith
  have hmono : Real.exp 18 ≤ Real.exp (6 * Real.pi) := Real.exp_le_exp.mpr h18
  have hsplit : Real.exp 18 = Real.exp 9 * Real.exp 9 := by
    rw [← Real.exp_add]; norm_num
  have h9 := ten_le_exp_nine
  nlinarith

/-- The deep-point value of `cosh` exceeds `10`. -/
lemma ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hc : Real.cosh (6 * Real.pi)
      = (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := Real.cosh_eq _
  have hpos : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  have h := twenty_lt_exp_six_pi
  rw [hc]
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`:
`(sinh (2π) / (2π))^2 * (1 - cosh (6π) / 10) < 0`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos_iff.mpr (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 :=
    pow_pos (div_pos hs (by linarith)) 2
  have hbr : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := ten_lt_cosh_six_pi
    linarith
  exact mul_neg_of_pos_of_neg hsq hbr

end Zeta23Obstruction

