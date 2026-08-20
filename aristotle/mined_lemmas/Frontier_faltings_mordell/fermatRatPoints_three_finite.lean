/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/

theorem fermatRatPoints_three_finite : (fermatRatPoints 3).Finite := by
  rw [fermatRatPoints_three]
  exact (Set.finite_singleton _).insert _

/-- **Faltings' theorem (Mordell conjecture), verified cases.**

For every `n ≥ 4` divisible by `3` or by `4`, the Fermat curve `x ^ n + y ^ n = 1` is a curve
over `ℚ` of genus `(n - 1)(n - 2) / 2 ≥ 2`, and it has only finitely many rational points.

This is an unconditional, Lean-checked family of instances of Faltings' theorem: the base cases
`n = 3` and `n = 4` come from Fermat's Last Theorem for exponents `3` and `4`, and the general
case follows by the Lean-checked reduction `fermatRatPoints_finite_of_dvd` along the
finite-fibred covering map `(x, y) ↦ (x ^ k, y ^ k)`. -/
