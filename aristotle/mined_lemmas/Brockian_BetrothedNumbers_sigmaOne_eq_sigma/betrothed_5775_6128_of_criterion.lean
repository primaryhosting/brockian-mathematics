import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/

theorem betrothed_5775_6128_of_criterion : IsBetrothedPair 5775 6128 := by
  have hp : Nat.Prime 383 := by norm_num
  have h : IsBetrothedPair 5775 (2 ^ 4 * 383) := by
    refine isBetrothedPair_of_sigma_criterion hp (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · rw [sigmaOne_5775]; norm_num
    · norm_num
  norm_num at h
  exact h

/-- The generating data: `383` is prime, `6128 = 2 ^ 4 * 383`, and both members have
sum of divisors `(2 ^ 5 - 1) * (383 + 1) = 5775 + 6128 + 1`. -/
