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

theorem MersennePrimeInfinitude : MersenneExponents.Infinite ↔ EvenPerfects.Infinite := by
  rw [Set.infinite_iff_exists_gt, Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h N
    have hp' : (mersenne p).Prime := hp
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := by
      cases p with
      | zero => simp [mersenne, Nat.not_prime_zero] at hp'
      | succ k => exact ⟨k, rfl⟩
    refine ⟨2 ^ k * mersenne (k + 1), ⟨even_two_pow_mul_mersenne hp',
      perfect_two_pow_mul_mersenne hp'⟩, ?_⟩
    calc N < k + 1 := hNp
      _ ≤ mersenne (k + 1) := self_le_mersenne _
      _ ≤ 2 ^ k * mersenne (k + 1) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
  · intro h N
    obtain ⟨n, ⟨hev, hperf⟩, hNn⟩ := h (2 ^ (2 * N + 1))
    obtain ⟨k, hk, rfl⟩ := eq_two_pow_mul_mersenne_of_even_perfect hev hperf
    have hlt : 2 ^ (2 * N + 1) < 2 ^ (2 * k + 1) := lt_trans hNn (two_pow_mul_mersenne_lt k)
    have : 2 * N + 1 < 2 * k + 1 := by
      by_contra hcon
      exact absurd (Nat.pow_le_pow_right (by norm_num) (by omega)) (not_le.mpr hlt)
    exact ⟨k + 1, hk, by omega⟩

/-- The set of Mersenne primes is infinite exactly when the set of their exponents is. -/
