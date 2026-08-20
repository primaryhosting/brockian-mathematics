/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The elementary statement of Fermat's Last Theorem: for every exponent `n ≥ 3`,
the equation `x ^ n + y ^ n = z ^ n` has no solution in positive integers. -/

theorem FLT_statement_four : FLTStatementFor 4 :=
  (FLTStatementFor_iff_fermatLastTheoremFor 4).2 fermatLastTheoremFour

/-- **Lean-checked reduction of Fermat's Last Theorem to odd prime exponents.**

The full statement of Fermat's Last Theorem — no positive integers `x, y, z` satisfy
`x ^ n + y ^ n = z ^ n` for any exponent `n ≥ 3` — is *equivalent* to its special case
for odd prime exponents.  The nontrivial direction combines the case `n = 4`
(Fermat's descent) with the fact that every `n > 2` is divisible by `4` or by an odd prime. -/
