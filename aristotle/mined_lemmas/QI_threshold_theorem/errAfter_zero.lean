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

/-- `errAfter C p L` is the logical error rate of a gate location after `L` levels of
code concatenation, in the standard fault-tolerance recursion: one level of encoding
turns a physical error rate `q` into a logical error rate `C * q ^ 2`, where `C` counts
the number of pairs of fault locations in one level-1 rectangle. -/

@[simp] lemma errAfter_zero (C p : ℝ) : errAfter C p 0 = p := rfl

