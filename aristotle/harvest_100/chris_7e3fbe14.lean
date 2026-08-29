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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- `exp 18 ≥ 100`, via `exp 9 ≥ 10`. -/
lemma hundred_le_exp_eighteen : (100 : ℝ) ≤ Real.exp 18 := by
  have h9 : (10 : ℝ) ≤ Real.exp 9 := by
    have := Real.add_one_le_exp (9 : ℝ)
    linarith
  have : Real.exp 9 * Real.exp 9 = Real.exp 18 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (9 : ℝ)]

/-- The hyperbolic cosine at `6π` exceeds `10`. -/
lemma ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) ≤ Real.pi := by
    have := Real.pi_gt_three
    linarith
  have h1 : (18 : ℝ) ≤ 6 * Real.pi := by linarith
  have h2 : Real.exp 18 ≤ Real.exp (6 * Real.pi) := Real.exp_le_exp.mpr h1
  have h3 : (100 : ℝ) ≤ Real.exp (6 * Real.pi) :=
    le_trans hundred_le_exp_eighteen h2
  have hcosh : Real.cosh (6 * Real.pi)
      = (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := by
    rw [Real.cosh_eq]
  have hpos : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  rw [hcosh]
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`:
`(sinh(2π)/(2π))² · (1 − cosh(6π)/10) < 0`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : 0 < Real.sinh (2 * Real.pi) := by
    rw [Real.sinh_pos_iff]; linarith
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by
    apply pow_pos
    exact div_pos hs (by linarith)
  have hbr : (1 : ℝ) - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := ten_lt_cosh_six_pi
    linarith
  exact mul_neg_of_pos_of_neg hsq hbr

end Zeta23Obstruction

