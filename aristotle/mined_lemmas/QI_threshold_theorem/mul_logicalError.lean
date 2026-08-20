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

import Mathlib
/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Filter Topology

/-- `logicalError C p k` is the effective (logical) error rate of a physical error rate `p`
after `k` levels of code concatenation, where one level of concatenation maps an error rate
`q` to `C * q ^ 2` (a block of the code fails only when at least two of its components fail,
and `C` counts the number of such failing pairs of locations). -/

theorem mul_logicalError (C p : ℝ) (k : ℕ) :
    C * logicalError C p k = (C * p) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have : C * logicalError C p (k + 1) = (C * logicalError C p k) ^ 2 := by
        simp only [logicalError_succ]; ring
      rw [this, ih, ← pow_mul, pow_succ]

/-- Explicit doubly-exponential suppression of the logical error rate. -/
