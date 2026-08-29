/-!
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

/-- `cosh (6π) > 10`. -/
lemma ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h3 : (1 : ℝ) + 3 * Real.pi ≤ Real.exp (3 * Real.pi) :=
    Real.add_one_le_exp _ |>.trans_eq' (by ring)
  have h10 : (10 : ℝ) < Real.exp (3 * Real.pi) := by nlinarith
  have hsq : Real.exp (6 * Real.pi) = Real.exp (3 * Real.pi) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hpos : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  have hc : Real.cosh (6 * Real.pi)
      = (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := by
    rw [Real.cosh_eq]
  rw [hc, hsq]
  nlinarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : 0 < Real.sinh (2 * Real.pi) := Mathlib.Meta.Positivity.sinh_pos_of_pos (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by positivity
  have hb : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := ten_lt_cosh_six_pi
    linarith
  exact mul_neg_of_pos_of_neg hsq hb

end Zeta23Obstruction

#print axioms Zeta23Obstruction.repaired_witness_neg_at_deep_point

