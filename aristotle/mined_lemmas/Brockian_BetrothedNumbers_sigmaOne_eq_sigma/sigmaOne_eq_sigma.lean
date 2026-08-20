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

theorem sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  rw [sigmaOne, ArithmeticFunction.sigma_one_apply]

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals the sum of the two numbers plus one. -/
