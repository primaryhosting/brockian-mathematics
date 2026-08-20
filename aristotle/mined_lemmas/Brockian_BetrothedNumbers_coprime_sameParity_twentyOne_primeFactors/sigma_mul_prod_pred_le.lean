import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- Notation for the sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-! ## Definition -/

/-- A *betrothed* (or *quasi-amicable*) pair: two positive integers each of whose
sum of divisors equals the sum of the two numbers plus one. -/

lemma sigma_mul_prod_pred_le {n : ℕ} (hn : n ≠ 0) :
    σ₁ n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  have h1 : σ₁ n = ∏ p ∈ n.primeFactors, σ₁ (p ^ n.factorization p) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn]; rfl
  have h2 : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rfl
  calc σ₁ n * ∏ p ∈ n.primeFactors, (p - 1)
      = ∏ p ∈ n.primeFactors, (σ₁ (p ^ n.factorization p) * (p - 1)) := by
        rw [h1, Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) := by
        refine Finset.prod_le_prod' ?_
        intro p hp
        calc σ₁ (p ^ n.factorization p) * (p - 1) ≤ p ^ (n.factorization p + 1) :=
              sigma_primePow_mul_pred_le p _ (Nat.prime_of_mem_primeFactors hp)
          _ = p ^ n.factorization p * p := by ring
    _ = n * ∏ p ∈ n.primeFactors, p := by rw [Finset.prod_mul_distrib, h2]

/-- An odd number whose abundancy index exceeds `4` has at least twenty-one distinct
prime factors. -/
