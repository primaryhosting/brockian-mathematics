import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex
open scoped Real

namespace Frontier

/-- `s` is a *trivial* zero of the Riemann zeta function, i.e. `s = -2, -4, -6, …`. -/

def IsTrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- `s` is a *nontrivial* zero of the Riemann zeta function: a zero of `ζ` which is not one of
the trivial zeros `-2, -4, -6, …`. -/
