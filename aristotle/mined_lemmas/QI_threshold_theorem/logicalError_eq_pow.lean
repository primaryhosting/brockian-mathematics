import Mathlib

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
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

namespace QI

/-- The logical error rate of a circuit location after `L` levels of code
concatenation, given a physical error rate `p` and a constant `c` counting the
number of malignant pairs of fault locations in one level-1 gadget.

One level of concatenation replaces each location by a gadget that fails only if
at least two of its locations fail, giving the standard recursion
`p_{L+1} = c * p_L ^ 2`. -/

lemma logicalError_eq_pow (c p : ℝ) (hc : c ≠ 0) (L : ℕ) :
    logicalError c p L = (c * p) ^ (2 ^ L) / c := by
  induction L with
  | zero => simp [mul_div_cancel_left₀ p hc]
  | succ L ih =>
      rw [logicalError_succ, ih, pow_succ 2 L, pow_mul]
      field_simp

/-- **Threshold theorem** (quantitative core).

`p_th = 1 / c` is a constant error threshold: if the physical error rate `p`
satisfies `p < p_th` (equivalently `c * p < 1`), then by concatenating the code
enough times the logical error rate can be made smaller than any prescribed
accuracy `ε > 0`, and it stays below `ε` for every larger number of levels.
Hence fault-tolerant quantum computation to arbitrary accuracy is possible below
the threshold. -/
