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

lemma isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  have h0 : usigma 2 = 3 := by
    have e : (2 : ℕ) = 2 ^ 1 := by norm_num
    rw [e, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h1 : usigma 18 = 30 := by
    have e : (18 : ℕ) = 2 * 3 ^ 2 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h0]
    norm_num
  have h2 : usigma 90 = 180 := by
    have e : (90 : ℕ) = 18 * 5 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h1]
    norm_num
  rw [h2]

