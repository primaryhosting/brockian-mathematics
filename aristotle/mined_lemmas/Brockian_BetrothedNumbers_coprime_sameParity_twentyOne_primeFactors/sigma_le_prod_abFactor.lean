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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/

lemma sigma_le_prod_abFactor {N : ℕ} (hN : N ≠ 0) :
    ((sigma 1 N : ℕ) : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, abFactor p := by
  have h1 : (sigma 1) N = ∏ p ∈ N.primeFactors, (sigma 1) (p ^ N.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hN]
    rfl
  have h2 : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rfl
  rw [h1]
  push_cast
  calc ∏ p ∈ N.primeFactors, ((sigma 1) (p ^ N.factorization p) : ℚ)
      ≤ ∏ p ∈ N.primeFactors, ((p:ℚ) ^ N.factorization p * abFactor p) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _; positivity
        · intro i hi
          exact_mod_cast sigma_primePow_le (Nat.prime_of_mem_primeFactors hi) _
    _ = (N : ℚ) * ∏ p ∈ N.primeFactors, abFactor p := by
        rw [Finset.prod_mul_distrib]
        congr 1
        conv_rhs => rw [h2]
        push_cast
        ring

/-! ## The product of `p/(p-1)` over at most twenty odd primes is less than four -/

