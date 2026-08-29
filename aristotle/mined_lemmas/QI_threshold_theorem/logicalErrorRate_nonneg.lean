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

lemma logicalErrorRate_nonneg (C p : ℝ) (hC : 0 < C) (hp : 0 ≤ p) (k : ℕ) :
    0 ≤ logicalErrorRate C p k := by
  rw [logicalErrorRate_eq C p hC.ne' k]
  positivity

/-- Below threshold (`C * p < 1`) the level-`k` error rates are non-increasing in `k`. -/
