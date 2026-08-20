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

theorem riemannZeta_eq_zero_of_isTrivialZero {s : ℂ} (hs : IsTrivialZero s) :
    riemannZeta s = 0 := by
  obtain ⟨n, rfl⟩ := hs
  exact riemannZeta_neg_two_mul_nat_add_one n

/-- Base case / known part of RH, right edge: `ζ` has no zeros in the closed half-plane
`1 ≤ Re s`. -/
