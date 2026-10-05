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

def GeneratedBySigmaCriterion (k p m n : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ n = 2 ^ k * p ∧ 0 < m ∧ m ≠ n ∧
    m + n + 1 = (2 ^ (k + 1) - 1) * (p + 1) ∧ sigmaOne m = (2 ^ (k + 1) - 1) * (p + 1)

/-- Any pair produced by the sigma criterion is indeed a betrothed pair. -/
