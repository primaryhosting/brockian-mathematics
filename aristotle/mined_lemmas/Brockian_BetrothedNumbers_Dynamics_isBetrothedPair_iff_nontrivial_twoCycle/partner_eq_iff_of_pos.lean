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

lemma partner_eq_iff_of_pos {n k : ℕ} (hk : 0 < k) :
    partner n = k ↔ sigma 1 n = n + k + 1 := by
  unfold partner
  omega

/-- **Betrothed pairs are exactly the nontrivial 2-cycles of `partner`
supported on the positive integers.**

`(m, n)` is a betrothed pair iff `m > 0`, `partner m = n`, `partner n = m`
and `m ≠ n`.  (Positivity of `n` is automatic: `partner 0 = 0`, so a
`partner`-cycle through `0` cannot reach a positive number.) -/
