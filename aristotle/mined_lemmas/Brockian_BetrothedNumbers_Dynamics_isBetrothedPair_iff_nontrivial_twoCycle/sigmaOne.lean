import Mathlib

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option autoImplicit false

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`, i.e. `ArithmeticFunction.sigma 1`. -/

noncomputable def sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

