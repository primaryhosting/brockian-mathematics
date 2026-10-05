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

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Betrothed (quasi-amicable) pairs -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals `m + n + 1`; equivalently `s(m) = n + 1` and `s(n) = m + 1`, where `s`
denotes the sum of the proper divisors. -/

theorem sigma_one_le_prod_primeFactors {N : ℕ} (hN : N ≠ 0) :
    ((σ 1 N : ℚ)) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
  have hmul : σ 1 N = N.factorization.prod fun p k => σ 1 (p ^ k) :=
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hN
  rw [Finsupp.prod, Nat.support_factorization] at hmul
  have hNeq : (N : ℚ) = ∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    ring
  rw [hmul, hNeq, ← Finset.prod_mul_distrib]
  push_cast
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  exact sigma_one_prime_pow_le (Nat.prime_of_mem_primeFactors hp)

/-! ## An elementary bound on Euler products over sets of odd primes -/

/-- The first twenty odd primes. -/
