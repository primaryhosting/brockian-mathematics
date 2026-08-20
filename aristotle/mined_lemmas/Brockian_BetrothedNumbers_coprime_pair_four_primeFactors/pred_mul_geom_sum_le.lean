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
open scoped Nat
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `Betrothed m n` says that `m` and `n` form a pair of betrothed (quasi-amicable)
numbers: they are distinct positive integers each of whose sum of divisors equals
`m + n + 1` (equivalently, the sum of the *proper* divisors of each, excluding `1`
and the number itself, is the other number). -/

lemma pred_mul_geom_sum_le (p k : ℕ) : (p - 1) * ∑ i ∈ Finset.range k, p ^ i ≤ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · rw [Finset.sum_range_succ, Nat.mul_add, pow_succ]
        have h1 : (p - 1) * p ^ k + p ^ k = p * p ^ k := by
          have : (p - 1) * p ^ k + 1 * p ^ k = (p - 1 + 1) * p ^ k := by ring
          simp only [one_mul] at this
          rw [this, Nat.sub_add_cancel hp]
        calc (p - 1) * ∑ i ∈ Finset.range k, p ^ i + (p - 1) * p ^ k
            ≤ p ^ k + (p - 1) * p ^ k := Nat.add_le_add_right ih _
          _ = p * p ^ k := by omega
          _ = p ^ k * p := by ring

/-- The basic abundancy bound: `σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`. -/
