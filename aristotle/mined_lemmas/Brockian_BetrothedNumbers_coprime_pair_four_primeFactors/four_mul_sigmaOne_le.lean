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

lemma four_mul_sigmaOne_le (N : ℕ) (hN : N ≠ 0) (hcard : N.primeFactors.card ≤ 3) :
    4 * sigmaOne N ≤ 15 * N := by
  have h1 := sigmaOne_mul_prod_pred_le N hN
  have h2 := four_prod_le_of_card_le_three N.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have key : (4 * sigmaOne N) * ∏ p ∈ N.primeFactors, (p - 1)
      ≤ (15 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by
    calc (4 * sigmaOne N) * ∏ p ∈ N.primeFactors, (p - 1)
        = 4 * (sigmaOne N * ∏ p ∈ N.primeFactors, (p - 1)) := by ring
      _ ≤ 4 * (N * ∏ p ∈ N.primeFactors, p) := by exact Nat.mul_le_mul_left _ h1
      _ = N * (4 * ∏ p ∈ N.primeFactors, p) := by ring
      _ ≤ N * (15 * ∏ p ∈ N.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ h2
      _ = (15 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right key hpos

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors. -/
