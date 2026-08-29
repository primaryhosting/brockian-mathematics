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

theorem generated_5775_6128 : GeneratedBySigmaCriterion 4 383 5775 6128 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [sigmaOne_5775]
  norm_num

/-- **Main result.** `(5775, 6128)` is a betrothed (quasi-amicable) pair, obtained from the
sigma criterion with `k = 4`, `p = 383`. -/
