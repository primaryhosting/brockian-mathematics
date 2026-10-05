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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the "aliquot sum"). -/

def sumProperDivisors (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `m` and `n` form an amicable pair: they are distinct and each is the sum of the
proper divisors of the other. -/
