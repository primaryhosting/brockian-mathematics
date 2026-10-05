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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.WilsonPrimes

open Nat

/-- A *Wilson prime* is a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`.
By Wilson's theorem, every prime `p` satisfies `p ∣ (p - 1)! + 1`; a Wilson prime
is one for which the stronger, squared divisibility holds. -/

lemma wilsonPrimeSet_nonempty : wilsonPrimeSet.Nonempty :=
  ⟨5, wilsonPrime_five⟩

/--
**Wilson prime infinitude, as a reduction.**

Whether there are infinitely many Wilson primes is an open problem; this theorem establishes
the exact equivalence between the two standard formulations of that statement: the set of
Wilson primes is infinite if and only if there are arbitrarily large Wilson primes.
-/
