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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem sigma_lt_two_mul_of_superperfect {n : ℕ} (hn : 1 < n) (h : Superperfect n) :
    σ 1 n < 2 * n := by
  have h1 : n + 1 ≤ σ 1 n := succ_le_sigma hn
  have h2 : σ 1 n + 1 ≤ σ 1 (σ 1 n) := succ_le_sigma (by omega)
  rw [h] at h2
  omega

/-- The sum of divisors of a superperfect number is never a power of two. -/
