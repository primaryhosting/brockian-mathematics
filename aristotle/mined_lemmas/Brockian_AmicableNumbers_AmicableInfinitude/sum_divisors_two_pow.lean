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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the divisors of `n` other than `n` itself). -/

lemma sum_divisors_two_pow (m : ℕ) : (∑ d ∈ (2 ^ m).divisors, d) + 1 = 2 ^ (m + 1) := by
  have h : ∑ d ∈ (2 ^ m).divisors, d = 2 ^ (m + 1) - 1 := by
    rw [← sigma_one_apply, sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq le_rfl]
    simp
  have h2 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  omega

/-- Sum of divisors versus sum of proper divisors. -/
