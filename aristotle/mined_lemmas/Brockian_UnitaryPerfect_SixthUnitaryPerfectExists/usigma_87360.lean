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

theorem usigma_87360 : usigma 87360 = 174720 := by
  have h13 : usigma 13 = 14 := by rw [usigma_prime (p := 13) (by norm_num)]
  have h7 : usigma 91 = 112 := by
    rw [show (91 : ℕ) = 7 * 13 by norm_num,
      usigma_prime_mul (p := 7) (by norm_num) (by norm_num) (by norm_num), h13]
  have h5 : usigma 455 = 672 := by
    rw [show (455 : ℕ) = 5 * 91 by norm_num,
      usigma_prime_mul (p := 5) (by norm_num) (by norm_num) (by norm_num), h7]
  have h3 : usigma 1365 = 2688 := by
    rw [show (1365 : ℕ) = 3 * 455 by norm_num,
      usigma_prime_mul (p := 3) (by norm_num) (by norm_num) (by norm_num), h5]
  rw [show (87360 : ℕ) = 2 ^ 6 * 1365 by norm_num,
    usigma_prime_pow_mul (p := 2) (k := 6) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h3]
  norm_num

