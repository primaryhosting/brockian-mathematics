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

def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

