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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
The infinitude of even perfect numbers is an open problem: by the Euclid–Euler theorem it is
equivalent to the infinitude of Mersenne primes, which is unknown.  What is proved here is
precisely that equivalence, in the form of a Lean-checked reduction:

* `Brockian.MersennePerfect.EvenPerfectInfinitude` : the set of even perfect numbers is infinite
  **iff** the set of Mersenne prime exponents is infinite.
* `Brockian.MersennePerfect.evenPerfect_infinite_of_mersenne_infinite` : the conditional form
  (infinitely many Mersenne primes ⟹ infinitely many even perfect numbers).
-/

namespace Brockian.MersennePerfect

open Nat

/-- The set of even perfect numbers. -/

theorem mersenne_infinite_of_evenPerfect_infinite (h : EvenPerfects.Infinite) :
    MersenneExponents.Infinite :=
  EvenPerfectInfinitude.mp h

/-- A sanity check that the sets involved are non-vacuous: `6` is an even perfect number,
witnessed by the Mersenne prime `3 = 2 ^ 2 - 1`. -/
