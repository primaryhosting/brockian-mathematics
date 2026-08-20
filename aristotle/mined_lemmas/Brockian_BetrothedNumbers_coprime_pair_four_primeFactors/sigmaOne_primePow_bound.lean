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

lemma sigmaOne_primePow_bound (p a : ℕ) (hp : p.Prime) :
    sigmaOne (p ^ a) * (p - 1) ≤ p ^ a * p := by
  have := sigmaOne_primePow_mul_pred p a hp
  have hp' : p ^ a * p = p ^ (a + 1) := (pow_succ p a).symm
  omega

/-- The basic abundancy bound: `σ₁ N / N ≤ ∏_{p ∣ N} p / (p - 1)`, in cleared-denominator form. -/
