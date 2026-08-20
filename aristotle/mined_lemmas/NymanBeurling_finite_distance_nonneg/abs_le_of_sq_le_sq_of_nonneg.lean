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

/-- Key intermediate lemma: if `p ^ 2 ≤ u ^ 2` and `0 ≤ u`, then `|p| ≤ u`. -/

lemma abs_le_of_sq_le_sq_of_nonneg {u p : ℝ} (h : p ^ 2 ≤ u ^ 2) (hu : 0 ≤ u) :
    |p| ≤ u := by
  nlinarith [abs_nonneg p, sq_abs p]

/-- Nyman–Beurling finite shape (scalar core): for real `u`, `p` with `p ^ 2 ≤ u ^ 2`
and `0 ≤ u`, the residual squared distance `u ^ 2 - p ^ 2` is nonnegative.

This is the scalar core of the statement that the squared distance from a unit vector
to a finite-dimensional subspace, `1 - ‖proj‖ ^ 2`, is nonnegative. -/
