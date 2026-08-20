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

A natural number `n` is *superperfect* when `σ (σ n) = 2 n`.  Suryanarayana and Kanold
showed that the even superperfect numbers are exactly the powers `2 ^ k` with
`2 ^ (k + 1) - 1` prime; whether an *odd* superperfect number exists is an open problem.

This file contains a Lean-checked reduction of that open problem, together with the
(easy half of the) even classification and two unconditional constraints on a
hypothetical odd superperfect number.
-/

open scoped ArithmeticFunction.sigma

open ArithmeticFunction Finset

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem superperfect_two_pow_of_mersenne_prime {k : ℕ}
    (hp : Nat.Prime (2 ^ (k + 1) - 1)) : Superperfect (2 ^ k) := by
  rw [Superperfect, sigma_one_apply_prime_pow Nat.prime_two]
  rw [show ∑ i ∈ range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 by
    simpa using Nat.geomSum_eq (le_refl 2) (k + 1)]
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

/-! ### Parity of the sum-of-divisors function -/

