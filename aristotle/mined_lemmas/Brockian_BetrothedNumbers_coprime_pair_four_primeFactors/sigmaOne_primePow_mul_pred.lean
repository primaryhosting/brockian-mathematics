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

lemma sigmaOne_primePow_mul_pred (p a : ℕ) (hp : p.Prime) :
    sigmaOne (p ^ a) * (p - 1) + 1 = p ^ (a + 1) := by
  have hgeom : sigmaOne (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [sigmaOne, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hgeom]
  exact geom_sum_mul_pred p a hp.two_le

/-- Termwise bound: `σ₁ (p ^ a) * (p - 1) ≤ p ^ a * p`. -/
