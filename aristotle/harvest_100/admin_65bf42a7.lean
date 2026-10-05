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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace NymanBeurling

/-- **Nyman–Beurling finite shape, scalar core.**

In a real inner product space, the squared distance from a unit vector `x` to a
finite-dimensional subspace equals `1 - ‖p‖ ^ 2`, where `p` is the orthogonal
projection of `x`; the Pythagorean identity `‖p‖ ^ 2 ≤ ‖x‖ ^ 2` then makes the
residual distance nonnegative.  This is the self-contained scalar core of that
statement: for reals `u`, `p` with `p ^ 2 ≤ u ^ 2` (and `0 ≤ u`), we have
`0 ≤ u ^ 2 - p ^ 2`.

The hypothesis `0 ≤ u` was requested in the statement; it turns out to be
unnecessary for the conclusion, but it is kept for faithfulness. -/
theorem finite_distance_nonneg (u p : ℝ) (hp : p ^ 2 ≤ u ^ 2) (hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 := by
  rcases eq_or_lt_of_le hu with _ | _ <;> exact sub_nonneg.mpr hp

end NymanBeurling

