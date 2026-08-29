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

theorem isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  refine (prod_primeFactors_pow_factorization hn).symm.trans
    (Finset.prod_congr rfl fun p _ => ?_)
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

/-- If `n` is odd with an odd sum of divisors, then every exponent in its prime factorization
is even. -/
