/-
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace NymanBeurling

/-- **Nyman–Beurling finite shape, scalar core.**

In a real inner product space, the squared distance from a unit vector to a
finite-dimensional subspace equals `1 - ‖P v‖ ^ 2`, where `P` is the orthogonal
projection; the Nyman–Beurling criterion states that the Riemann Hypothesis is
equivalent to these distances `d_N` tending to `0`.  This is the self-contained
scalar core of the nonnegativity part: if `p ^ 2 ≤ u ^ 2` then the residual
`u ^ 2 - p ^ 2` is nonnegative.

The hypothesis `0 ≤ u` is part of the requested statement (it records that `u`
is a norm) but is not needed for the conclusion; the proof is
`sub_nonneg.mpr hpu`. -/
theorem finite_distance_nonneg (u p : ℝ) (hpu : p ^ 2 ≤ u ^ 2) (hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 := by
  clear hu
  exact sub_nonneg.mpr hpu

end NymanBeurling

