import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `Betrothed m n` says that `m` and `n` are *betrothed* (quasi-amicable) numbers:
both are positive and each one's sum of divisors equals `m + n + 1`. -/

lemma sigma_mul_prod_pred_le {N : ℕ} (hN : N ≠ 0) :
    (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have hsig : (sigma 1) N = ∏ p ∈ N.primeFactors, (sigma 1) (p ^ N.factorization p) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hN]
    rw [Finsupp.prod, Nat.support_factorization]
  have hNfac : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
  calc (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, ((sigma 1) (p ^ N.factorization p) * (p - 1)) := by
        rw [hsig, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) := by
        refine Finset.prod_le_prod' ?_
        intro p hp
        exact sigma_primePow_mul_pred_le (Nat.prime_of_mem_primeFactors hp) _
    _ = N * ∏ p ∈ N.primeFactors, p := by
        rw [Finset.prod_mul_distrib, ← hNfac]

/-- Numeric core: `(A+1)(B+1)(C+1) ≤ 4·A·B·C` for `A ≥ 1`, `B ≥ 2`, `C ≥ 4`
(i.e. `2/1 · 3/2 · 5/4 = 15/4 ≤ 4`). -/
