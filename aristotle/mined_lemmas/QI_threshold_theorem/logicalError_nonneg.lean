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

/-
/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QI

/-- The logical error rate of a level-`L` concatenated code, in the standard
recursive model of fault tolerance: one level of concatenation replaces a physical
error rate `x` by `C * x ^ 2` (a logical failure requires at least two independent
failures among the constituent blocks, with `C` counting the malignant pairs).
`C` is the inverse of the accuracy threshold `p_th = 1 / C`. -/

theorem logicalError_nonneg {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (L : ℕ) :
    0 ≤ logicalError C p L := by
  induction L with
  | zero => simpa using hp
  | succ L _ => exact mul_nonneg hC (sq_nonneg _)

/--
**Threshold theorem, robust form.**

The conclusion does not depend on the error rates following the recursion exactly:
any nonnegative sequence `q` of level-`L` logical error rates that starts below the
threshold (`q 0 ≤ p < 1 / C`) and is suppressed at least quadratically at each level
(`q (L+1) ≤ C * q L ^ 2`) is bounded by the doubly exponentially decaying sequence
`p_th * (p / p_th) ^ (2 ^ L)` and therefore converges to `0`.
-/
