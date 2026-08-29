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

theorem sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply]
  rfl

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals `m + n + 1`. -/
