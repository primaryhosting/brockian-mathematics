import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate `m = (2^k - 1)(p + 2)`. -/

def thabitPartner (k p : ℕ) : ℕ := 2 ^ k * p

/-- The delivered sigma criterion: `m = (2^k - 1)(p + 2)` and its Thabit partner
`n = 2^k * p` form a betrothed (quasi-amicable) configuration for `m`, i.e.
`σ(m) = m + n + 1`. -/
