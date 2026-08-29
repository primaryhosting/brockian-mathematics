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

/-- The logical error rate of a fault-tolerant scheme built by `k`-fold concatenation of a
distance-3 (single-error-correcting) code, starting from physical error rate `p`.

One level of concatenation replaces each gate by a fault-tolerant gadget which fails only if at
least two of its constituent locations fail; with `C` the number of malignant pairs of locations
in a gadget, the standard level-reduction estimate gives
`p_{k+1} = C * p_k ^ 2`. -/

lemma logicalErrorRate_antitone (C p : ℝ) (hC : 0 < C) (hp : 0 ≤ p) (hlt : C * p < 1) (k : ℕ) :
    logicalErrorRate C p (k + 1) ≤ logicalErrorRate C p k := by
  have h0 : 0 ≤ logicalErrorRate C p k := logicalErrorRate_nonneg C p hC hp k
  have hle : C * logicalErrorRate C p k ≤ 1 := by
    rw [mul_logicalErrorRate]
    exact pow_le_one₀ (by positivity) hlt.le
  have : C * (logicalErrorRate C p k) ^ 2 ≤ 1 * logicalErrorRate C p k := by
    have := mul_le_mul_of_nonneg_right hle h0
    calc C * (logicalErrorRate C p k) ^ 2
        = (C * logicalErrorRate C p k) * logicalErrorRate C p k := by ring
      _ ≤ 1 * logicalErrorRate C p k := this
  simpa using this

/-- Below threshold, the logical error rate tends to `0` as the number of concatenation
levels tends to infinity (in fact doubly exponentially fast). -/
