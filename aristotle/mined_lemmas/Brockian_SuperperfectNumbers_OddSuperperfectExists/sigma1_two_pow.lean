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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`, where `σ` is the
sum-of-divisors function.  The known superperfect numbers are `2, 4, 16, 64, …`,
i.e. the numbers `2 ^ (p - 1)` for which `2 ^ p - 1` is a Mersenne prime.  Whether
an *odd* superperfect number exists is an open problem: none is known, and it is
conjectured that none exists.

Accordingly this file does not prove the (open) existence statement outright.
Instead it develops the basic theory of `σ` needed here and proves an
unconditional **reduction**: an odd superperfect number exists if and only if one
exists that is, in addition, larger than `500` and composite.  Both extra
constraints are proved for every odd superperfect number, so the reduction is a
genuine restriction of the search space, not a tautology.
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem sigma1_two_pow (a : ℕ) : sigma1 (2 ^ a) = 2 ^ (a + 1) - 1 := by
  rw [sigma1, Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [Nat.geomSum_eq]

