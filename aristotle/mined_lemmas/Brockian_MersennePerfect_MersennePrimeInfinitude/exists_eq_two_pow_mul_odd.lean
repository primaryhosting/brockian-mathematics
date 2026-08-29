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

theorem exists_eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) :
    ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬ Even m := by
  refine ⟨n.factorization 2, n / 2 ^ n.factorization 2,
    (Nat.ordProj_mul_ordCompl_eq_self n 2).symm, ?_⟩
  rw [even_iff_two_dvd]
  exact Nat.not_dvd_ordCompl Nat.prime_two hpos.ne'

/-- Euler's direction: every even perfect number has the shape `2 ^ k * (2 ^ (k+1) - 1)` with
`2 ^ (k+1) - 1` prime. -/
