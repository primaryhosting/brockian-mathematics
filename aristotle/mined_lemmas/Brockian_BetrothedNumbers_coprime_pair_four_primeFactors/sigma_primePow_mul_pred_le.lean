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

lemma sigma_primePow_mul_pred_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (sigma 1) (p ^ k) * (p - 1) ≤ p ^ k * p := by
  have hsum : (sigma 1) (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hsum]
  have := geom_sum_mul_pred p hp.one_lt.le k
  have hpk : p ^ (k + 1) = p ^ k * p := by ring
  omega

/-- The key abundancy bound: `σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`. -/
