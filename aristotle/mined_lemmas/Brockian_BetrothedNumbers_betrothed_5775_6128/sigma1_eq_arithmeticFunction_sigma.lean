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

set_option maxRecDepth 100000

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem sigma1_eq_arithmeticFunction_sigma (n : ℕ) :
    sigma1 n = ArithmeticFunction.sigma 1 n := by
  simp [sigma1, ArithmeticFunction.sigma_apply]

/-- `a` and `b` form a **betrothed** (quasi-amicable) pair: they are distinct positive
integers, each of which is the sum of the nontrivial proper divisors of the other,
equivalently `σ₁ a = σ₁ b = a + b + 1`. -/
