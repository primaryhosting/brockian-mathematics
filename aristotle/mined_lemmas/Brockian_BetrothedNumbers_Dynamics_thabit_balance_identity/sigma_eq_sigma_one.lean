/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers.Dynamics

open Finset

/-- The sum-of-divisors function `σ₁`. -/

@[simp] theorem sigma_eq_sigma_one (n : ℕ) :
    sigma n = ArithmeticFunction.sigma 1 n := by
  simp [sigma, ArithmeticFunction.sigma_apply]

/-- **Thabit shape.** `m` is the Thabit-type number `(2 ^ k - 1) * (p + 2)`, written in the
subtraction-free form `m + (p + 2) = 2 ^ k * (p + 2)`. -/
