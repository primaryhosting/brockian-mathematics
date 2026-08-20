import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` lines to be the very first commands in a file,
so the module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the imports is rejected by the parser).
-/

open Complex

namespace Frontier

/-- `s` is a *trivial zero* of the Riemann zeta function if it is one of the points
`-2, -4, -6, …`, at which `ζ` is known to vanish (`riemannZeta_neg_two_mul_nat_add_one`). -/

def IsTrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0` and `s` is not one of
the trivial zeros `-2, -4, -6, …`. -/
