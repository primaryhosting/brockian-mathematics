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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-! ## The statements -/

/-- `GoldbachPair n` : `n` is a sum of two primes. -/

def GoldbachModel (N : ℕ) : Prop := ∀ n : ℕ, 4 ≤ n → n ≤ N → Even n → GoldbachPair n

/-! ## The schema: a binary model reaches three primes for odd numbers beyond it -/

/-- **Schema.** A Goldbach model valid up to `N` yields a representation as a sum of three
primes for every odd number `n` with `9 ≤ n ≤ N + 3`, i.e. reaching `3` beyond the range
of the model. -/
