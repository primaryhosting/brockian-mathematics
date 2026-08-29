import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
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

namespace Brockian

/-- The list of all primes not exceeding the wheel modulus `947`. -/

theorem prime_of_mem_primesUpTo947 : ∀ p ∈ primesUpTo947, Nat.Prime p := by decide

/-- The finite Goldbach search: every `n < 474` with `n ≥ 2` gives an even number `2 * n`
that splits as a sum of two entries of `primesUpTo947`. -/
