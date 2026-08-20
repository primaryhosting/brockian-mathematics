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

theorem logicalError_closed_form (C p : ℝ) (L : ℕ) :
    C * logicalError C p L = (C * p) ^ (2 ^ L) := by
  induction L with
  | zero => simp
  | succ L ih =>
      have : C * logicalError C p (L + 1) = (C * logicalError C p L) ^ 2 := by
        simp [logicalError]; ring
      rw [this, ih, ← pow_mul, pow_succ]

/--
**Threshold theorem** (concatenated-code form).

Let `p_th = 1 / C > 0` be the accuracy threshold of a fault-tolerant scheme whose
level-by-level error suppression obeys `p_{L+1} = C * p_L ^ 2`. If the physical
error rate `p` is nonnegative and strictly *below* the threshold, then:

* the level-`L` logical error rate is given exactly by
  `p_L = p_th * (p / p_th) ^ (2 ^ L)`, i.e. it decreases *doubly exponentially* in
  the number `L` of concatenation levels;
* consequently `p_L → 0`, so for every target accuracy `ε > 0` there is a level `L`
  achieving logical error below `ε`: arbitrarily accurate quantum computation is
  possible below the threshold.
-/
