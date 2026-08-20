import Mathlib
/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The *betrothed partner map*: `partner n = σ₁ n - n - 1`, i.e. the sum of the
divisors of `n` that are strictly between `1` and `n` (subtraction is truncated). -/

theorem partner_def (n : ℕ) : partner n = ArithmeticFunction.sigma 1 n - n - 1 := rfl

/-- Betrothed pairs are exactly the positive nontrivial `2`-cycles of the partner map
`partner n = σ₁ n - n - 1`. -/
