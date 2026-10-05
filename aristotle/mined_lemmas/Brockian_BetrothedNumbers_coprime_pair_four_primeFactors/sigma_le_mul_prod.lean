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

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n` such that
the sum of the divisors of each equals `m + n + 1`, i.e. each is the sum of the *nontrivial*
divisors (excluding `1` and the number itself) of the other. -/

lemma sigma_le_mul_prod {N : ℕ} (hN : N ≠ 0) :
    ((sigma 1 N : ℕ) : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
  have h1 : ((sigma 1 N : ℕ) : ℚ)
      = ∏ p ∈ N.primeFactors, ((sigma 1 (p ^ N.factorization p) : ℕ) : ℚ) := by
    conv_lhs => rw [isMultiplicative_sigma.multiplicative_factorization _ hN]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  have h2 : (N : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) ^ N.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  exact sigma_primePow_le p _ (Nat.prime_of_mem_primeFactors hp)

/-- Elementary bounds on the local Euler factor `p/(p-1)` of a prime `p`. -/
