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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- `cosh (6π) > 10`: from `cosh x ≥ exp x / 2` and `exp (6π) = (exp (3π))^2 ≥ (1 + 3π)^2 > 100`. -/
lemma ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1' : (1 : ℝ) + 3 * Real.pi ≤ Real.exp (3 * Real.pi) := by
    have := Real.add_one_le_exp (3 * Real.pi)
    linarith
  have hpos : (0 : ℝ) < 1 + 3 * Real.pi := by nlinarith
  have hsq : (1 + 3 * Real.pi) ^ 2 ≤ Real.exp (3 * Real.pi) ^ 2 :=
    pow_le_pow_left₀ hpos.le h1' 2
  have hexp : Real.exp (6 * Real.pi) = Real.exp (3 * Real.pi) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h20 : (20 : ℝ) < Real.exp (6 * Real.pi) := by
    rw [hexp]
    nlinarith
  have hcosh : Real.exp (6 * Real.pi) / 2 ≤ Real.cosh (6 * Real.pi) := by
    rw [Real.cosh_eq]
    have : (0 : ℝ) < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
    linarith
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsinh : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos_iff.mpr (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by
    exact pow_pos (div_pos hsinh (by linarith)) 2
  have hb : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := ten_lt_cosh_six_pi
    linarith
  exact mul_neg_of_pos_of_neg hsq hb

end Zeta23Obstruction

