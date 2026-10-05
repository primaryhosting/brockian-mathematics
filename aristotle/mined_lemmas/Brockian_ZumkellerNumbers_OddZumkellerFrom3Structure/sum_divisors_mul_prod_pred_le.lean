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
/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks having the same sum. -/

theorem sum_divisors_mul_prod_pred_le (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      ≤ n * ∏ p ∈ n.primeFactors, p := by
  calc (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      = ∏ p ∈ n.primeFactors, ((∑ d ∈ (p ^ n.factorization p).divisors, d) * (p - 1)) := by
        rw [sum_divisors_eq_prod n hn, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) :=
        Finset.prod_le_prod' fun p hp =>
          sigma_prime_pow_mul_pred_le p _ (Nat.prime_of_mem_primeFactors hp)
    _ = n * ∏ p ∈ n.primeFactors, p := by
        rw [Finset.prod_mul_distrib, ← self_eq_prod_primeFactors_pow n hn]

/-- Two distinct odd numbers `≥ 3` satisfy `p * q < 2 * ((p - 1) * (q - 1))`. -/
