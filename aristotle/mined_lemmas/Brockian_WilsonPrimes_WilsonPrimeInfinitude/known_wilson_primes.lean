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

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`.
(By Wilson's theorem, `p` itself always divides `(p - 1)! + 1` when `p` is prime,
so a Wilson prime is one for which this divisibility holds to the second power.) -/

theorem known_wilson_primes : ({5, 13, 563} : Set ℕ) ⊆ {p : ℕ | IsWilsonPrime p} := by
  rintro p (rfl | rfl | rfl)
  · exact isWilsonPrime_five
  · exact isWilsonPrime_thirteen
  · exact isWilsonPrime_563

/-- The set of Wilson primes is infinite precisely when it is unbounded. -/
