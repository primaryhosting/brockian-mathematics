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

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of even perfect numbers is equivalent to the infinitude of Mersenne primes,
which is a well-known open problem.  What is proved here is therefore the (unconditional)
*reduction*: the set of even perfect numbers is infinite **iff** the set of exponents `p`
with `2 ^ p - 1` prime is infinite.

The Euclid–Euler development below (`sigma_two_pow_eq_mersenne_succ`,
`perfect_two_pow_mul_mersenne_of_prime`, `eq_two_pow_mul_prime_mersenne_of_even_perfect`,
`even_and_perfect_iff`) follows the proof of Theorem 70 of the 100 theorems list as
developed by Aaron Anderson in the Mathlib `Archive` (Apache 2.0); it is reproduced here
because the `Archive` is not part of the importable `Mathlib` library.
-/

namespace Brockian.MersennePerfect

open Nat ArithmeticFunction Finset

open scoped sigma

/-! ## The Euclid–Euler theorem -/


theorem euclidMap_injective : Function.Injective euclidMap :=
  euclidMap_strictMono.injective

/-- Euclid–Euler, in the form of a set equality: the even perfect numbers are exactly the
images under `euclidMap` of the exponents `k` with `2 ^ (k + 1) - 1` prime. -/
