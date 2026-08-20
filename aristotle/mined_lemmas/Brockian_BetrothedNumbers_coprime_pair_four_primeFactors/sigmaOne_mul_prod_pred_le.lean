/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `σ₁ n` is the sum of divisors of `n`. -/

lemma sigmaOne_mul_prod_pred_le (N : ℕ) (hN : N ≠ 0) :
    sigmaOne N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have h1 : sigmaOne N = ∏ p ∈ N.primeFactors, sigmaOne (p ^ N.factorization p) := by
    rw [sigmaOne, ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hN,
      Finsupp.prod, Nat.support_factorization]
    rfl
  have h2 : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
  have h3 : ∏ p ∈ N.primeFactors, (sigmaOne (p ^ N.factorization p) * (p - 1))
      ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := by
    refine Finset.prod_le_prod' ?_
    intro p hp
    exact sigmaOne_primePow_bound p _ (Nat.prime_of_mem_primeFactors hp)
  calc sigmaOne N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, (sigmaOne (p ^ N.factorization p) * (p - 1)) := by
        rw [h1, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := h3
    _ = (∏ p ∈ N.primeFactors, p ^ N.factorization p) * ∏ p ∈ N.primeFactors, p := by
        rw [Finset.prod_mul_distrib]
    _ = N * ∏ p ∈ N.primeFactors, p := by rw [← h2]

/-- Three increasing primes: `4 * a * b * c ≤ 15 * (a-1) * (b-1) * (c-1)`. -/
