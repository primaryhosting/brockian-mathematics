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

lemma four_le_card_primeFactors_of_abundancy {N : ℕ} (hN : N ≠ 0) (h : 4 * N < (sigma 1) N) :
    4 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have h3 : N.primeFactors.card ≤ 3 := by omega
  have hprimes : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (hprimes p hp).two_le
    omega
  have hA := sigma_mul_prod_pred_le hN
  have hB := prod_le_four_mul_prod_pred hprimes h3
  have hC : N * ∏ p ∈ N.primeFactors, p ≤ N * (4 * ∏ p ∈ N.primeFactors, (p - 1)) :=
    Nat.mul_le_mul_left _ hB
  have hD : (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1)
      ≤ (4 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by
    calc (sigma 1) N * ∏ p ∈ N.primeFactors, (p - 1)
        ≤ N * (4 * ∏ p ∈ N.primeFactors, (p - 1)) := le_trans hA hC
      _ = (4 * N) * ∏ p ∈ N.primeFactors, (p - 1) := by ring
  have := Nat.le_of_mul_le_mul_right hD hpos
  omega

/-- Hagis–Lord, Proposition 2: if `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors. -/
