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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum of the proper divisors of `n` (all divisors of `n` other than `n` itself). -/

theorem sigma1_two_pow (m : ℕ) : sigma1 (2 ^ m) + 1 = 2 ^ (m + 1) := by
  have h : sigma1 (2 ^ m) = ∑ i ∈ Finset.range (m + 1), 2 ^ i := by
    unfold sigma1
    exact Nat.sum_divisors_prime_pow Nat.prime_two
  rw [h, geom_two]

