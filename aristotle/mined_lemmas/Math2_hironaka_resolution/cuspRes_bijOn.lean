import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

namespace Math2

/-- The affine cuspidal cubic `{(x, y) | y ^ 2 = x ^ 3}` over a field `k`. -/

lemma cuspRes_bijOn : Set.BijOn (cuspRes k) Set.univ (cuspCurve k) :=
  ⟨fun t _ => cuspRes_mem t, Set.injOn_of_injective cuspRes_injective, cuspRes_surjOn⟩

/-- The singular locus of the cuspidal cubic (in characteristic `0`) is exactly the origin:
the gradient `(-3 x ^ 2, 2 y)` of `y ^ 2 - x ^ 3` vanishes at a point of the curve iff that
point is the origin. -/
