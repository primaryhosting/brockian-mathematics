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

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the "aliquot sum"). -/

lemma isAmicablePair_iff_sigma {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    IsAmicablePair m n ↔ m ≠ n ∧ σ 1 m = m + n ∧ σ 1 n = m + n := by
  have hm' : σ 1 m = sumProperDivisors m + m := by
    rw [ArithmeticFunction.sigma_one_apply, sumProperDivisors,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hn' : σ 1 n = sumProperDivisors n + n := by
    rw [ArithmeticFunction.sigma_one_apply, sumProperDivisors,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
  unfold IsAmicablePair
  rw [hm', hn']
  omega

/-- `σ₁` of a power of two. -/
