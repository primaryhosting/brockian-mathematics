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

theorem prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- If all exponents in the prime factorization of `n ≠ 0` are even, then `n` is a square. -/
