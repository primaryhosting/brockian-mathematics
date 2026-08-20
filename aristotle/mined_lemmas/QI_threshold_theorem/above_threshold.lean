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

theorem above_threshold {c p : ℝ} (hc : 0 < c) (hthr : 1 / c < p) :
    Tendsto (fun k : ℕ => logicalErrorRate c p k) atTop atTop := by
  have hq1 : 1 < c * p := by
    have := (div_lt_iff₀' hc).1 hthr
    linarith
  have h1 : Tendsto (fun n : ℕ => (c * p) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq1
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℕ))
  have h3 : Tendsto (fun k : ℕ => (c * p) ^ (2 ^ k)) atTop atTop := h1.comp h2
  have : Tendsto (fun k : ℕ => (c * p) ^ (2 ^ k) / c) atTop atTop :=
    h3.atTop_div_const hc
  simpa [logicalErrorRate_eq c p hc.ne'] using this

end QI

