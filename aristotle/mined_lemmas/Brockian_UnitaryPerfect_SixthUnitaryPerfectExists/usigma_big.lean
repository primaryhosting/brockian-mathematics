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

A *unitary divisor* of `n` is a divisor `d` with `gcd d (n / d) = 1`, and `n` is *unitary
perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.  Exactly five unitary
perfect numbers are known:

`6`, `60`, `90`, `87360`, `146361946186458562560000`,

and whether a sixth one exists is an open problem.  This file develops the basic theory
(`σ*` is multiplicative, `σ*(p^a) = 1 + p^a`, the factorization formula), verifies the five
known examples, proves that every unitary perfect number is even, and reduces the existence
of a sixth unitary perfect number to an explicit arithmetic criterion on the odd part.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem usigma_big : usigma 146361946186458562560000 = 292723892372917125120000 := by
  have h11 : usigma 313 = 314 := by rw [usigma_prime (p := 313) (by norm_num)]
  have h10 : usigma 49141 = 49612 := by
    rw [show (49141 : ℕ) = 157 * 313 by norm_num,
      usigma_prime_mul (p := 157) (by norm_num) (by norm_num) (by norm_num), h11]
  have h9 : usigma 5356369 = 5457320 := by
    rw [show (5356369 : ℕ) = 109 * 49141 by norm_num,
      usigma_prime_mul (p := 109) (by norm_num) (by norm_num) (by norm_num), h10]
  have h8 : usigma 423153151 = 436585600 := by
    rw [show (423153151 : ℕ) = 79 * 5356369 by norm_num,
      usigma_prime_mul (p := 79) (by norm_num) (by norm_num) (by norm_num), h9]
  have h7 : usigma 15656666587 = 16590252800 := by
    rw [show (15656666587 : ℕ) = 37 * 423153151 by norm_num,
      usigma_prime_mul (p := 37) (by norm_num) (by norm_num) (by norm_num), h8]
  have h6 : usigma 297476665153 = 331805056000 := by
    rw [show (297476665153 : ℕ) = 19 * 15656666587 by norm_num,
      usigma_prime_mul (p := 19) (by norm_num) (by norm_num) (by norm_num), h7]
  have h5 : usigma 3867196646989 = 4645270784000 := by
    rw [show (3867196646989 : ℕ) = 13 * 297476665153 by norm_num,
      usigma_prime_mul (p := 13) (by norm_num) (by norm_num) (by norm_num), h6]
  have h4 : usigma 42539163116879 = 55743249408000 := by
    rw [show (42539163116879 : ℕ) = 11 * 3867196646989 by norm_num,
      usigma_prime_mul (p := 11) (by norm_num) (by norm_num) (by norm_num), h5]
  have h3 : usigma 297774141818153 = 445945995264000 := by
    rw [show (297774141818153 : ℕ) = 7 * 42539163116879 by norm_num,
      usigma_prime_mul (p := 7) (by norm_num) (by norm_num) (by norm_num), h4]
  have h2 : usigma 186108838636345625 = 279162193035264000 := by
    rw [show (186108838636345625 : ℕ) = 5 ^ 4 * 297774141818153 by norm_num,
      usigma_prime_pow_mul (p := 5) (k := 4) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), h3]
    norm_num
  have h1 : usigma 558326515909036875 = 1116648772141056000 := by
    rw [show (558326515909036875 : ℕ) = 3 * 186108838636345625 by norm_num,
      usigma_prime_mul (p := 3) (by norm_num) (by norm_num) (by norm_num), h2]
  rw [show (146361946186458562560000 : ℕ) = 2 ^ 18 * 558326515909036875 by norm_num,
    usigma_prime_pow_mul (p := 2) (k := 18) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h1]
  norm_num

