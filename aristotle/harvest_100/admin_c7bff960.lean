/-
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Scalar core of the Nyman–Beurling finite-dimensional distance identity:
if the squared projection length `p ^ 2` does not exceed the squared norm `u ^ 2`
of a (nonnegative) vector length `u`, then the residual squared distance
`u ^ 2 - p ^ 2` is nonnegative.

The hypothesis `0 ≤ u` is kept because it is part of the requested statement,
although the conclusion follows from `hpu` alone. -/
theorem finite_distance_nonneg (u p : ℝ) (hpu : p ^ 2 ≤ u ^ 2) (hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 := by
  -- `hu` is part of the requested statement but is not needed for the conclusion.
  have _ : (0 : ℝ) ≤ u := hu
  linarith

end NymanBeurling

