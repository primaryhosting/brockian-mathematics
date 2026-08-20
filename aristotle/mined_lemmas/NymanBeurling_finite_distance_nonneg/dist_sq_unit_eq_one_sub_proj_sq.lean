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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace NymanBeurling

/-- **Scalar core of the Nyman–Beurling finite shape.**

If `p ^ 2 ≤ u ^ 2` (the squared norm of the projection is at most the squared norm of the
vector), then the residual squared distance `u ^ 2 - p ^ 2` is nonnegative.

The hypothesis `0 ≤ u` is included as requested in the statement of the problem; it is not
needed for the conclusion. -/

theorem dist_sq_unit_eq_one_sub_proj_sq (K : Submodule ℝ E) [FiniteDimensional ℝ K] {x : E}
    (hx : ‖x‖ = 1) :
    ‖x - K.starProjection x‖ ^ 2 = 1 - ‖K.starProjection x‖ ^ 2 := by
  have h := norm_sq_eq_residual_add_proj K x
  rw [hx] at h
  linarith

/-- The squared distance from a unit vector to a finite-dimensional subspace lies in `[0, 1]`. -/
