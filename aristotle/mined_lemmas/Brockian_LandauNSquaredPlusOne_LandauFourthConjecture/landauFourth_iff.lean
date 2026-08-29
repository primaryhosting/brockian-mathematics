import Brockian.LandauNSquaredPlusOne

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

/-
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.LandauNSquaredPlusOne

open Set

/-- The set of primes of the form `n ^ 2 + 1` (the "Landau primes"). -/

theorem landauFourth_iff : UnboundedLandauWitnesses ↔ LandauPrimes.Infinite :=
  ⟨LandauFourthConjecture, unboundedLandauWitnesses_of_infinite⟩

/-- The set of witnesses: naturals `n` for which `n ^ 2 + 1` is prime. -/
