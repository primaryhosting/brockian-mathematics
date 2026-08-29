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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Whether there are infinitely many Mersenne primes is a well-known open problem, so no
unconditional proof is attempted here.  What is proved is an *unconditional equivalence*:

  there are infinitely many Mersenne primes  ↔  there are infinitely many even perfect numbers.

The equivalence rests on the Euclid–Euler theorem, which is developed from scratch below
(`Brockian.MersennePerfect.even_and_perfect_iff`), together with an explicit size estimate
translating "unboundedly large even perfect numbers" into "unboundedly large Mersenne
exponents".

The main statement `Brockian.MersennePerfect.MersennePrimeInfinitude` is this equivalence.
Two conditional corollaries are also recorded.
-/

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-- The set of exponents `p` for which `mersenne p = 2 ^ p - 1` is prime. -/

theorem two_pow_mul_mersenne_lt (k : ℕ) : 2 ^ k * mersenne (k + 1) < 2 ^ (2 * k + 1) := by
  have h : mersenne (k + 1) < 2 ^ (k + 1) := by
    have : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
    simp only [mersenne]
    omega
  calc 2 ^ k * mersenne (k + 1) < 2 ^ k * 2 ^ (k + 1) := by gcongr
    _ = 2 ^ (2 * k + 1) := by rw [← pow_add]; ring_nf

/-! ### The main equivalence -/

/-- **Mersenne prime infinitude, reduced to even perfect numbers.**

There are infinitely many Mersenne primes if and only if there are infinitely many even
perfect numbers.  (Both sides are open problems; the content here is the unconditional
equivalence, via the Euclid–Euler theorem.) -/
