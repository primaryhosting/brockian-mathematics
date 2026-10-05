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

lemma geom_sum_mul_pred (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), p ^ i) * (p - 1) + 1 = p ^ (k + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      set A := ∑ i ∈ Finset.range (k + 1), (q + 1) ^ i with hA
      set P := (q + 1) ^ (k + 1) with hP
      calc (A + P) * q + 1 = (A * q + 1) + P * q := by ring
        _ = P + P * q := by rw [ih]
        _ = (q + 1) ^ (k + 1 + 1) := by rw [hP]; ring

/-- Prime-power abundancy bound: `σ(p ^ k) * (p - 1) ≤ p ^ k * p`. -/
