import Mathlib
/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
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

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when the image of `a` in `ZMod p` has
multiplicative order exactly `p - 1`, i.e. it generates the group of units of `ZMod p`. -/

theorem finite_primitiveRootPrimes_of_isSquare {a : ℤ} (hsq : IsSquare a) :
    (primitiveRootPrimes a).Finite := by
  apply Set.Finite.subset (Set.finite_singleton 2)
  rintro p ⟨hp, h⟩
  exact eq_two_of_isSquare_of_isPrimitiveRootMod hp hsq h

