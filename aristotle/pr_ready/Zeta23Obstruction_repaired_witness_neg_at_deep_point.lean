/-!
# Repaired Witness Neg At Deep Point
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
Statement: The repaired witness kernel is strictly negative at the deep point 2i: (sinh 2π/2π)²·(1 − cosh(6π)/10) < 0 — the deep-pair blowup is real.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
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

set_option grind.warning false

namespace Zeta23Obstruction

/-- `exp (3π) ≥ 10`, from `exp x ≥ x + 1` and `π > 3`. -/
lemma exp_three_pi_ge_ten : (10 : ℝ) ≤ Real.exp (3 * Real.pi) := by
  have h1 : (3 : ℝ) * Real.pi + 1 ≤ Real.exp (3 * Real.pi) := Real.add_one_le_exp _
  have h2 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  linarith

/-- `cosh (6π) > 10`. -/
lemma cosh_six_pi_gt_ten : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hexp : (100 : ℝ) ≤ Real.exp (6 * Real.pi) := by
    have : Real.exp (6 * Real.pi) = Real.exp (3 * Real.pi) * Real.exp (3 * Real.pi) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    nlinarith [exp_three_pi_ge_ten, Real.exp_pos (3 * Real.pi)]
  have hcosh : Real.cosh (6 * Real.pi) =
      (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := by
    rw [Real.cosh_eq]
  have hneg : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  rw [hcosh]
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`. -/
theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsinh : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos_iff.mpr (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 :=
    pow_pos (div_pos hsinh (by linarith)) 2
  have hbr : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := cosh_six_pi_gt_ten
    linarith
  exact mul_neg_of_pos_of_neg hsq hbr

end Zeta23Obstruction

