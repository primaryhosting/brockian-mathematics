/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The betrothed (quasi-amicable) partner map: `partner n = σ₁(n) - n - 1`,
the sum of the proper divisors of `n` other than `1`.  Natural subtraction is
harmless here: for `n ≥ 2` one has `σ₁(n) ≥ n + 1`. -/

@[simp] lemma partner_zero : partner 0 = 0 := by
  simp [partner]

/-- For positive `n`, `σ₁(n) - n - 1 = k` with `k > 0` is equivalent to
`σ₁(n) = n + k + 1`; this removes all truncated-subtraction issues. -/
