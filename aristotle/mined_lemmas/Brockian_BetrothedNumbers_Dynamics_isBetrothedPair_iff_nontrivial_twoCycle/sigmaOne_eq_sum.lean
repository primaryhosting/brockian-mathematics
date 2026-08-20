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

lemma sigmaOne_eq_sum (n : ℕ) : sigmaOne n = ∑ d ∈ n.divisors, d := by
  simp [sigmaOne, ArithmeticFunction.sigma_one_apply]

/-- The *betrothed partner* map: `partner n = σ₁(n) - n - 1`, i.e. the sum of the
divisors of `n` other than `1` and `n` itself. -/
