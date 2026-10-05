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

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- Geometric sum identity in `ℕ`, phrased so as to avoid truncated subtraction. -/

lemma sigma_lt_four_mul_of_card_le_three {N : ℕ} (hN : N ≠ 0)
    (hcard : N.primeFactors.card ≤ 3) : sigma 1 N < 4 * N := by
  have h1 := sigma_mul_prod_pred_le hN
  have h2 : 4 * ∏ p ∈ N.primeFactors, p ≤ 15 * ∏ p ∈ N.primeFactors, (p - 1) :=
    prod_bound_of_card_le_three (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have h3 : 4 * (sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)) ≤ N * (4 * ∏ p ∈ N.primeFactors, p) := by
    calc 4 * (sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1))
        ≤ 4 * (N * ∏ p ∈ N.primeFactors, p) := by exact Nat.mul_le_mul_left _ h1
      _ = N * (4 * ∏ p ∈ N.primeFactors, p) := by ring
  have h4 : N * (4 * ∏ p ∈ N.primeFactors, p) ≤ N * (15 * ∏ p ∈ N.primeFactors, (p - 1)) :=
    Nat.mul_le_mul_left _ h2
  have h5 : (4 * sigma 1 N) * (∏ p ∈ N.primeFactors, (p - 1))
      ≤ (15 * N) * (∏ p ∈ N.primeFactors, (p - 1)) := by
    calc (4 * sigma 1 N) * (∏ p ∈ N.primeFactors, (p - 1))
        = 4 * (sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)) := by ring
      _ ≤ N * (15 * ∏ p ∈ N.primeFactors, (p - 1)) := le_trans h3 h4
      _ = (15 * N) * (∏ p ∈ N.primeFactors, (p - 1)) := by ring
  have h6 : 4 * sigma 1 N ≤ 15 * N := Nat.le_of_mul_le_mul_right h5 hpos
  omega

/-- `m` and `n` are *betrothed* (quasi-amicable) numbers: they are distinct and each has
divisor sum equal to `m + n + 1`. -/
