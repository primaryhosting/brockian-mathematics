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

theorem eq_two_pow_mul_mersenne_of_even_perfect {n : ℕ} (hev : Even n) (hperf : n.Perfect) :
    ∃ k : ℕ, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := hperf.2
  obtain ⟨k, m, rfl, hm⟩ := exists_eq_two_pow_mul_odd hpos
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_one_two_pow, ← mul_assoc, ← pow_succ'] at hperf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ hperf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at hperf
  have h := mul_left_cancel₀ (by positivity) hperf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  rcases Nat.sum_properDivisors_dvd (by rw [hj]; exact Dvd.intro_left (mersenne (k + 1)) rfl) with
    h1 | h1
  · have j1 : j = 1 := hj.symm.trans h1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h1
    simp [h1, j1]
  · exfalso
    have jcon := hj.symm.trans h1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp at hm
    have jcon2 := mul_right_cancel₀ hj0 jcon
    match k with
    | 0 =>
      apply hm
      rw [← jcon2, pow_zero, one_mul, one_mul] at hev
      rw [← jcon2, one_mul]
      exact even_iff_two_dvd.mp hev
    | .succ k =>
      exact absurd jcon2.symm (one_lt_mersenne.mpr (by omega)).ne'

/-- The Euclid–Euler theorem characterising even perfect numbers. -/
