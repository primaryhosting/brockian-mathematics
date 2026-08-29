/-
# Repaired Witness Neg At Deep Point
Category: Brockian Corpus
Target: Zeta23Obstruction.repaired_witness_neg_at_deep_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `exp 18` is at least `343 = 7 ^ 3`, from `1 + x ≤ exp x`. -/

lemma exp_eighteen_ge : (343 : ℝ) ≤ Real.exp 18 := by
  have h6 : (7 : ℝ) ≤ Real.exp 6 := by
    have := Real.add_one_le_exp (6 : ℝ)
    linarith
  have hsplit : Real.exp 18 = Real.exp 6 * (Real.exp 6 * Real.exp 6) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (6 : ℝ)]

/-- `cosh (6π) > 10`. -/
