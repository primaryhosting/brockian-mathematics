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

/-- `exp 18 ≥ 343`, obtained from `exp 6 ≥ 7` (i.e. `1 + x ≤ exp x`) cubed. -/
lemma exp_eighteen_ge : (343 : ℝ) ≤ Real.exp 18 := by
  have h6 : (7 : ℝ) ≤ Real.exp 6 := by
    have := Real.add_one_le_exp (6 : ℝ)
    linarith
  have h : Real.exp 18 = (Real.exp 6) ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  calc (343 : ℝ) = 7 ^ 3 := by norm_num
    _ ≤ (Real.exp 6) ^ 3 := by
        gcongr

/-- `cosh (6π) > 10`. -/
lemma cosh_six_pi_gt_ten : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hmono : Real.exp 18 ≤ Real.exp (6 * Real.pi) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hneg : (0 : ℝ) < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  have hcosh : Real.cosh (6 * Real.pi)
      = (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := by
    rw [Real.cosh_eq]
  rw [hcosh]
  have := exp_eighteen_ge
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsinh : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos_iff.mpr (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by
    apply pow_pos
    exact div_pos hsinh (by linarith)
  have hbr : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := cosh_six_pi_gt_ten
    linarith
  exact mul_neg_of_pos_of_neg hsq hbr

end Zeta23Obstruction

