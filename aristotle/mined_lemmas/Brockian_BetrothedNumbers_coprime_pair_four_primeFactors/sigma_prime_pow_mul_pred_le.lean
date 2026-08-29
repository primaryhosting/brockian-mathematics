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

lemma sigma_prime_pow_mul_pred_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) * (p - 1) ≤ p ^ a * p := by
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hgs := geom_sum_mul_succ q a
  rw [sigma_prime_pow _ _ hp]
  simp only [Nat.add_sub_cancel]
  calc (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q
      ≤ (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q + 1 := Nat.le_succ _
    _ = (q + 1) ^ (a + 1) := hgs
    _ = (q + 1) ^ a * (q + 1) := by ring

/-- The global bound `σ(N) * ∏_{p ∣ N} (p-1) ≤ N * ∏_{p ∣ N} p`. -/
