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

set_option grind.warning false

namespace Zeta23Obstruction

/-- `exp 18 ≥ 100`, from `1 + x ≤ exp x` applied at `x = 9`. -/

lemma cosh_six_pi_gt_ten : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h18 : (18 : ℝ) ≤ 6 * Real.pi := by linarith
  have hmono : Real.exp 18 ≤ Real.exp (6 * Real.pi) := Real.exp_le_exp.mpr h18
  have hcosh : Real.cosh (6 * Real.pi)
      = (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := by
    rw [Real.cosh_eq]
  have hpos : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  have := exp_eighteen_ge
  rw [hcosh]
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`. -/
