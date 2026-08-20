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
lemma ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h18 : (18 : ℝ) ≤ 6 * Real.pi := by linarith
  have hmono : Real.exp 18 ≤ Real.exp (6 * Real.pi) := Real.exp_le_exp.mpr h18
  have h6 : (7 : ℝ) ≤ Real.exp 6 := seven_le_exp_six
  have hcube : Real.exp 18 = (Real.exp 6) ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpos : (0 : ℝ) < Real.exp 6 := Real.exp_pos _
  have h343 : (343 : ℝ) ≤ Real.exp 18 := by
    rw [hcube]
    calc (343 : ℝ) = 7 ^ 3 := by norm_num
      _ ≤ (Real.exp 6) ^ 3 := by gcongr
  have hneg : (0 : ℝ) < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  rw [Real.cosh_eq]
  linarith

theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos_iff.mpr (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by
    apply pow_pos
    positivity
  have hb : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := ten_lt_cosh_six_pi
    linarith
  exact mul_neg_of_pos_of_neg hsq hb

end Zeta23Obstruction

