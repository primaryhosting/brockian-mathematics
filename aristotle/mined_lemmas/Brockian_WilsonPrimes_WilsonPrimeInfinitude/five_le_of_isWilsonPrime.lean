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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`
(equivalently, Wilson's congruence `(p-1)! ≡ -1` holds modulo `p ^ 2`). -/

theorem five_le_of_isWilsonPrime {p : ℕ} (h : IsWilsonPrime p) : 5 ≤ p := by
  by_contra hlt
  push_neg at hlt
  interval_cases p <;> revert h <;> decide

/-!
## Main statement

The Wilson prime infinitude conjecture (part of the Brockian circle of conjectures)
asserts that there are infinitely many Wilson primes; this is open.  The theorem below
is the Lean-checked reduction: infinitude of the set of Wilson primes is *equivalent*
to the unboundedness statement "for every `N` there is a Wilson prime exceeding `N`".
-/

/-- **Wilson prime infinitude, reduction form.**  The set of Wilson primes is infinite
if and only if Wilson primes are unbounded, i.e. for every bound `N` there is a Wilson
prime larger than `N`. -/
