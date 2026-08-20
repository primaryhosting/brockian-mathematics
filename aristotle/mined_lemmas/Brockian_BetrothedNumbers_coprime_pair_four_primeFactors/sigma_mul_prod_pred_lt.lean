import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma sigma_mul_prod_pred_lt {n : ℕ} (hn : 1 < n) :
    σ 1 n * ∏ p ∈ n.primeFactors, (p - 1) < n * ∏ p ∈ n.primeFactors, p := by
  have hn0 : n ≠ 0 := by omega
  have hsig : σ 1 n = ∏ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)]
    simp
  have hnprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
    rfl
  rw [hsig, ← Finset.prod_mul_distrib]
  have hrhs : n * ∏ p ∈ n.primeFactors, p
      = ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) := by
    rw [Finset.prod_mul_distrib, ← hnprod]
  rw [hrhs]
  refine Finset.prod_lt_prod_of_nonempty ?_ ?_ (Nat.nonempty_primeFactors.mpr hn)
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : 0 < σ 1 (p ^ n.factorization p) :=
      ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hpp.pos.ne')
    have h2 : 0 < p - 1 := by have := hpp.two_le; omega
    exact Nat.mul_pos h1 h2
  · intro p hp
    exact sigma_prime_pow_mul_pred_lt (Nat.prime_of_mem_primeFactors hp) _

/-- Two distinct primes: `a * b ≤ 4 * ((a-1) * (b-1))`, given `2 ≤ a`, `3 ≤ b`. -/
