/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers with `σ m = σ n = m + n + 1`. -/

lemma sigma_mul_prod_pred_le {N : ℕ} (hN : N ≠ 0) :
    sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have h1 : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) := by
    rw [(isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hN]; rfl
  have h2 : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
  calc sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p) * (p - 1)) := by
        rw [h1, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) :=
        Finset.prod_le_prod' fun q hq =>
          sigma_primePow_mul_pred_le (Nat.prime_of_mem_primeFactors hq) _
    _ = N * ∏ p ∈ N.primeFactors, p := by rw [Finset.prod_mul_distrib, h2]

/-- For a set of at most three primes, `∏ p ≤ 4 * ∏ (p - 1)`; the extremal case
`{2, 3, 5}` gives `∏ p/(p-1) = 15/4 < 4`. -/
