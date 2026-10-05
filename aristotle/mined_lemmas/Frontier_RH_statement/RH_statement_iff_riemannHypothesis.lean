/-
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 requires `import` commands to
-- precede any module docstring; the docstring form is repeated immediately after the import.)

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real

namespace Frontier

/-
The Riemann Hypothesis itself is an open problem, so `RH_statement` is *stated* here (and shown
to agree with Mathlib's `RiemannHypothesis`) rather than proved. What is proved below,
unconditionally and axiom-cleanly, is:

* the zero-free regions `Re s ≤ 0` (only trivial zeros) and `Re s ≥ 1` (no zeros), i.e. every
  nontrivial zero lies in the critical strip `0 < Re s < 1`;
* the symmetry `s ↦ 1 - s` of the set of nontrivial zeros, coming from the functional equation;
* the resulting reduction: RH is equivalent to the one-sided statement that no nontrivial zero
  has `Re s > 1/2` (and, symmetrically, to `Re s < 1/2` being excluded).
-/

/-- A complex number `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0`,
`s` is not one of the trivial zeros `-2, -4, -6, …`, and `s ≠ 1` (the point `s = 1` is a pole,
where Mathlib's `riemannZeta` takes a junk value). -/

theorem RH_statement_iff_riemannHypothesis : RH_statement ↔ RiemannHypothesis := by
  constructor
  · intro h s hs h1 h2
    exact h s ⟨hs, h1, h2⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

/-- Every zero of `ζ` with non-positive real part is a trivial zero `-2(n+1)`. -/
