import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The sum of all (positive) divisors of `n`, i.e. `σ₁ n`. -/

lemma sigmaSum_eq_sigma_one (n : ℕ) : sigmaSum n = sigma 1 n := (sigma_one_apply n).symm

/-- `σ₁ (2 ^ k) = 2 ^ (k + 1) - 1`. -/
