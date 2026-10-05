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

theorem sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  rw [sigmaOne_eq_sigma]
  have : p = p ^ 1 := (pow_one p).symm
  rw [this, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, add_comm]

/-- **The sigma criterion.** For an odd prime `p`, `σ₁(2 ^ k * p) = (2 ^ (k+1) - 1) * (p + 1)`. -/
