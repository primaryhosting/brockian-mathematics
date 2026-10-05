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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the divisors of `n` other than `n` itself). -/

lemma amicable_220_284 : Amicable 220 284 := by
  have h : ThabitTriple 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have := amicable_of_thabitTriple (n := 1) le_rfl h
  norm_num at this
  exact this

/-- **Conditional infinitude of amicable numbers.**
If there are infinitely many `n` for which the Thabit ibn Qurra triple
`3·2ⁿ-1`, `3·2ⁿ⁺¹-1`, `9·2²ⁿ⁺¹-1` consists of primes, then there are infinitely many
amicable pairs: for every bound `N` there is an amicable pair `(a, b)` with both
`a` and `b` exceeding `N`. -/
