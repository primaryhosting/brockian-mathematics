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

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose sum of
divisors equals their sum plus one. -/

lemma sigma_one_le_mul_prod_primeFactors {N : ℕ} (hN : N ≠ 0) :
    ((σ 1 N : ℕ) : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1) := by
  have hfac : ((N : ℕ) : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) ^ (N.factorization p)) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod]
    push_cast [Nat.support_factorization]
    rfl
  have hsig : ((σ 1 N : ℕ) : ℚ)
      = ∏ p ∈ N.primeFactors, ((σ 1 (p ^ (N.factorization p)) : ℕ) : ℚ) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hN]
    push_cast [Nat.support_factorization]
    rfl
  rw [hsig, hfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) ?_
  intro p hp
  exact sigma_one_prime_pow_le (Nat.prime_of_mem_primeFactors hp) _

/-! ### Bounding `∏ p/(p-1)` over a set of at most twenty odd primes -/

/-- If there is no prime strictly between `a` and `b`, then every prime above `a` is `≥ b`. -/
