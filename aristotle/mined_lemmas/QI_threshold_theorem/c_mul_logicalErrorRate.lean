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
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

open Filter Topology

/-- `logicalErrorRate c p k` is the failure probability of a logical gate protected by `k`
levels of code concatenation, in the standard recursive model of fault tolerance:
a level-`0` (unencoded) gate fails with probability `p`, and a level-`(k+1)` gate fails only if
at least two of its level-`k` constituent blocks fail, which happens with probability at most
`c * (level-k failure rate)^2`, where `c` counts the malignant pairs of fault locations in the
fault-tolerant gadget. -/

theorem c_mul_logicalErrorRate (c p : ℝ) (k : ℕ) :
    c * logicalErrorRate c p k = (c * p) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
      rw [logicalErrorRate_succ, h, pow_mul, ← ih]
      ring

/-- The error rate at level `k`, explicitly. -/
