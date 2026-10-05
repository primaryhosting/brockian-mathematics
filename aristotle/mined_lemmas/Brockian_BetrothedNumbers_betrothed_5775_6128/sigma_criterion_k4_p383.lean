/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem sigma_criterion_k4_p383 :
    Nat.Prime 383 ∧ (6128 : ℕ) = 2 ^ 4 * 383 ∧
      sigmaOne 6128 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      (5775 : ℕ) = (2 ^ (4 + 1) - 1) * (383 + 1) - 6128 - 1 := by
  refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩
  have h : (6128 : ℕ) = 2 ^ 4 * 383 := by norm_num
  rw [h, sigmaOne_two_pow_mul_prime (by norm_num) (by norm_num)]

/-- The betrothed pair `(5775, 6128)` obtained from the `k = 4, p = 383` criterion,
without any brute-force computation of `σ₁ 6128`. -/
