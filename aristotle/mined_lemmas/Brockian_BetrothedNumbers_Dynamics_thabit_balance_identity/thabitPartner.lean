import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate `m = (2^k - 1) * (p + 2)`. -/

def thabitPartner (k p : ℕ) : ℕ := 2 ^ k * p

/-- The delivered (subtraction-free) sigma criterion for the Thabit-style pair:
`σ(m) = (2^(k+1) - 1)(p + 1)`. -/
