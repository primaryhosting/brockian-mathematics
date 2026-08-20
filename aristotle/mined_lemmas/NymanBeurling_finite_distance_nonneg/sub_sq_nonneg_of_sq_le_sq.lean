import Mathlib

/-!
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
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

namespace NymanBeurling

/-- Key intermediate lemma: if `p ^ 2 ≤ u ^ 2` then the difference `u ^ 2 - p ^ 2`
is nonnegative. -/

lemma sub_sq_nonneg_of_sq_le_sq {u p : ℝ} (h : p ^ 2 ≤ u ^ 2) : 0 ≤ u ^ 2 - p ^ 2 :=
  sub_nonneg.mpr h

/-- **Nyman–Beurling finite shape, scalar core.**
For real numbers `u p` with `p ^ 2 ≤ u ^ 2` and `0 ≤ u`, the residual
`u ^ 2 - p ^ 2` (the squared distance from a vector of norm `u` to a subspace, whose
projection has norm `p`) is nonnegative.

Note: the hypothesis `0 ≤ u` is part of the requested statement but is not needed
for the conclusion. -/
