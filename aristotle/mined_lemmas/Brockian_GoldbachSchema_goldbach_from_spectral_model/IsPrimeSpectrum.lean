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

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-- A *prime spectrum* of `n` is a multiset `s` of primes (the "spectral lines", with
multiplicity) whose total mass `s.sum` is exactly `n`. -/

def IsPrimeSpectrum (n : ℕ) (s : Multiset ℕ) : Prop :=
  (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n

/-- `n` admits a spectral model when it has a prime spectrum. -/
