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

lemma geom_sum_mul_pred (p a : ℕ) (hp2 : 2 ≤ p) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + 1 = p ^ (a + 1) := by
  induction a with
  | zero => simp; omega
  | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, add_assoc, add_comm (p ^ (k + 1) * (p - 1)) 1,
        ← add_assoc, ih]
      have : p ^ (k + 1) * (p - 1) = p ^ (k + 1 + 1) - p ^ (k + 1) := by
        rw [Nat.mul_sub, mul_one, pow_succ]
        congr 1
      rw [this]
      have h1 : p ^ (k + 1) ≤ p ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega

/-- `σ₁ (p ^ a) * (p - 1) + 1 = p ^ (a + 1)` for a prime `p`. -/
