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

The header above is repeated verbatim as the module docstring, since Lean does
not allow a doc comment to precede the import line.
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The *quasi-aliquot* (or "betrothed partner") function
`partner n = σ₁(n) - n - 1`, i.e. the sum of the proper divisors of `n`
excluding `1` (and excluding `n` itself).  Subtraction is truncated
subtraction on `ℕ`; for `n ≥ 2` we always have `n + 1 ≤ σ₁(n)`, so no
truncation occurs there. -/

lemma partner_eq_iff_sigma_eq {m n : ℕ} (hm : 0 < m) :
    partner n = m ↔ sigma 1 n = n + m + 1 := by
  unfold partner
  omega

/-- **Betrothed pairs are exactly the nontrivial positive 2-cycles of
`partner (n) = σ₁(n) - n - 1`.** -/
