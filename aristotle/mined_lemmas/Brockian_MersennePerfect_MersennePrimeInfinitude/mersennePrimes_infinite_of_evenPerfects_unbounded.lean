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

theorem mersennePrimes_infinite_of_evenPerfects_unbounded
    (h : ∀ N : ℕ, ∃ n ∈ EvenPerfects, N < n) : MersennePrimes.Infinite :=
  mersennePrimes_infinite_of_evenPerfects_infinite (Set.infinite_of_forall_exists_gt h)

/-! ### Sanity checks

The first few Mersenne exponents and the even perfect numbers they produce. -/

example : 2 ∈ MersenneExponents := by norm_num [MersenneExponents, mersenne]

example : 3 ∈ MersenneExponents := by norm_num [MersenneExponents, mersenne]

example : 5 ∈ MersenneExponents := by norm_num [MersenneExponents, mersenne]

example : (6 : ℕ) ∈ EvenPerfects := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]
  decide

example : (28 : ℕ) ∈ EvenPerfects := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]
  decide

example : (496 : ℕ) ∈ EvenPerfects :=
  even_and_perfect_iff.mpr ⟨4, by norm_num [mersenne], by norm_num [mersenne]⟩

end Brockian.MersennePerfect

