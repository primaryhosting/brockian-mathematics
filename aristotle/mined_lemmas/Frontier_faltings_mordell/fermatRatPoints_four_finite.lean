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

theorem fermatRatPoints_four_finite : (fermatRatPoints 4).Finite := by
  rw [fermatRatPoints_four]
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _

/-- **Base case.**  The rational points of the Fermat cubic `x ^ 3 + y ^ 3 = 1` are exactly
`(1, 0)` and `(0, 1)`.  This is a consequence of Fermat's Last Theorem for exponent `3`. -/
