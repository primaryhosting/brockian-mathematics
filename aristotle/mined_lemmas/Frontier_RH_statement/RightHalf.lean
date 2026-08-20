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

def RightHalf : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → 1 / 2 ≤ s.re

/-! ### Key intermediate lemma: reflection of nontrivial zeros -/

/-- The functional equation of `ζ` sends a zero in the critical strip to a zero in the
critical strip: if `s` is a nontrivial zero, then so is `1 - s`. -/
