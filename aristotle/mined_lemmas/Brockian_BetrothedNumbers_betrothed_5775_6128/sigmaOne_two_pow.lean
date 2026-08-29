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

theorem sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigmaOne_eq_sigma, ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  have := sum_two_pow_succ (k + 1)
  omega

/-- The sum of divisors of an odd prime `p` is `p + 1`. -/
