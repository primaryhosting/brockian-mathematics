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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n / d) = 1`, and `n` is *unitary
perfect* if the sum `σ*(n)` of its unitary divisors equals `2 n`.  Exactly five unitary
perfect numbers are known:

`6, 60, 90, 87360, 146361946186458562560000`,

and it is a long-standing open problem whether a sixth one exists.  Accordingly this file
does **not** prove unconditional existence; it develops the basic theory of `σ*`
(multiplicativity, values at prime powers), verifies that the five known numbers really are
unitary perfect, proves that every unitary perfect number is even, and finally proves the
target statement `SixthUnitaryPerfectExists` as a *conditional reduction*: any unitary
perfect number that either exceeds the largest known one or fails to be divisible by `3`
is a sixth unitary perfect number.

(The header comment above appears after the `import` line only because Lean requires
imports to come first in a file.)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

lemma isUnitaryPerfect_N5 : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have h0 : usigma 262144 = 262145 := by
    have e : (262144 : ℕ) = 2 ^ 18 := by norm_num
    rw [e, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h1 : usigma 786432 = 1048580 := by
    have e : (786432 : ℕ) = 262144 * 3 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h0]
    norm_num
  have h2 : usigma 491520000 = 656411080 := by
    have e : (491520000 : ℕ) = 786432 * 5 ^ 4 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h1]
    norm_num
  have h3 : usigma 3440640000 = 5251288640 := by
    have e : (3440640000 : ℕ) = 491520000 * 7 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h2]
    norm_num
  have h4 : usigma 37847040000 = 63015463680 := by
    have e : (37847040000 : ℕ) = 3440640000 * 11 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h3]
    norm_num
  have h5 : usigma 492011520000 = 882216491520 := by
    have e : (492011520000 : ℕ) = 37847040000 * 13 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h4]
    norm_num
  have h6 : usigma 9348218880000 = 17644329830400 := by
    have e : (9348218880000 : ℕ) = 492011520000 * 19 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h5]
    norm_num
  have h7 : usigma 345884098560000 = 670484533555200 := by
    have e : (345884098560000 : ℕ) = 9348218880000 * 37 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h6]
    norm_num
  have h8 : usigma 27324843786240000 = 53638762684416000 := by
    have e : (27324843786240000 : ℕ) = 345884098560000 * 79 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h7]
    norm_num
  have h9 : usigma 2978407972700160000 = 5900263895285760000 := by
    have e : (2978407972700160000 : ℕ) = 27324843786240000 * 109 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h8]
    norm_num
  have h10 : usigma 467610051713925120000 = 932241695455150080000 := by
    have e : (467610051713925120000 : ℕ) = 2978407972700160000 * 157 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h9]
    norm_num
  have h11 : usigma 146361946186458562560000 = 292723892372917125120000 := by
    have e : (146361946186458562560000 : ℕ) = 467610051713925120000 * 313 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h10]
    norm_num
  rw [h11]

