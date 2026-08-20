/-
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- A *nontrivial zero* of the Riemann zeta function: a zero lying in the open critical
strip `0 < Re s < 1`.  All other zeros of `ζ` are the *trivial* zeros `s = -2, -4, -6, …`
(see `Frontier.eq_trivial_zero_of_zero_of_re_le_zero` and
`Frontier.riemannHypothesis_iff`). -/

def CriticalLine : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2

/-- The one-sided form of the Riemann Hypothesis: no nontrivial zero lies strictly
to the left of the critical line. -/
