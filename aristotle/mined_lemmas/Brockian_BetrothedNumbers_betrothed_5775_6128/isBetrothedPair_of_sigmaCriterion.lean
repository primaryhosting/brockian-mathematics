/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem isBetrothedPair_of_sigmaCriterion {k p m n : ℕ}
    (h : GeneratedBySigmaCriterion k p m n) : IsBetrothedPair m n := by
  obtain ⟨hp, hp2, hn, hm, hmn, hsum, hsig⟩ := h
  have hσn : sigmaOne n = (2 ^ (k + 1) - 1) * (p + 1) := by
    rw [hn]; exact sigmaOne_two_pow_mul_prime hp hp2
  refine ⟨hm, ?_, hmn, ?_, ?_⟩
  · subst hn
    exact Nat.mul_pos (Nat.two_pow_pos k) hp.pos
  · rw [hsig, hsum]
  · rw [hσn, hsum]

set_option maxRecDepth 100000

