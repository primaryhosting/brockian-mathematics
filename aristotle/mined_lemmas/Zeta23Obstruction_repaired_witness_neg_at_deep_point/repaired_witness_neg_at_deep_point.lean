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

theorem repaired_witness_neg_at_deep_point :
    (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 *
      (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsinh : 0 < Real.sinh (2 * Real.pi) := Real.sinh_pos.mpr (by linarith)
  have hsq : 0 < (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 := by
    have : 0 < Real.sinh (2 * Real.pi) / (2 * Real.pi) := div_pos hsinh (by linarith)
    positivity
  have hbr : 1 - (1 / 10) * Real.cosh (6 * Real.pi) < 0 := by
    have := cosh_six_pi_gt_ten
    linarith
  exact mul_neg_of_pos_of_neg hsq hbr

end Zeta23Obstruction

