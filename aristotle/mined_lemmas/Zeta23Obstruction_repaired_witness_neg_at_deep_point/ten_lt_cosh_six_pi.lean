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

lemma ten_lt_cosh_six_pi : (10 : ℝ) < Real.cosh (6 * Real.pi) := by
  have hc : Real.cosh (6 * Real.pi)
      = (Real.exp (6 * Real.pi) + Real.exp (-(6 * Real.pi))) / 2 := Real.cosh_eq _
  have hpos : 0 < Real.exp (-(6 * Real.pi)) := Real.exp_pos _
  have h := twenty_lt_exp_six_pi
  rw [hc]
  linarith

/-- The repaired witness kernel is strictly negative at the deep point `2i`:
`(sinh (2π) / (2π))^2 * (1 - cosh (6π) / 10) < 0`. -/
