/-!
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
Statement: Nyman-Beurling finite shape: in a real inner product space, the squared distance from a unit vector to a finite-dimensional subspace equals 1 minus the squared norm of its projection, which is in [0,1]. State the self-contained scalar core: for all real u p with p^2 <= u^2 and 0 <= u, we have 0 <= u^2 - p^2 (the residual distance is nonnegative). (RH iff the Nyman-Beurling distances d_N -> 0.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

namespace NymanBeurling

/-- Scalar core of the Nyman–Beurling finite-shape estimate: for real `u`, `p`
with `p ^ 2 ≤ u ^ 2` and `0 ≤ u`, the residual `u ^ 2 - p ^ 2` is nonnegative.

The hypothesis `0 ≤ u` is part of the requested statement but is not needed for
the conclusion; the result follows from `sub_nonneg` applied to `h`. -/
theorem finite_distance_nonneg (u p : ℝ) (h : p ^ 2 ≤ u ^ 2) (hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 := by
  clear hu
  exact sub_nonneg.mpr h

end NymanBeurling

