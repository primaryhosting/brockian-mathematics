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

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GoldbachSchema

/-- `GoldbachBeyond N` says that *beyond* the bound `N` there is an even number which is a
sum of two distinct primes, i.e. the Goldbach representation property is witnessed at some
even number larger than `N`. -/

def GoldbachBeyond (N : ℕ) : Prop :=
  ∃ m p q : ℕ, N < m ∧ Even m ∧ Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p + q = m

/-- The "model" hypothesis of the schema: a Bertrand-type prime model, asserting that for every
positive `n` there is a prime in the interval `(n, 2n]`. -/
