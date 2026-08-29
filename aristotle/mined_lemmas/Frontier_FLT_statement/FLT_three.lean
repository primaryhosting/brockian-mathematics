-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with *positive* integers:
there are no `x, y, z > 0` with `x ^ n + y ^ n = z ^ n`. -/

theorem FLT_three : FLTFor 3 := (FLTFor_iff_fermatLastTheoremFor 3).2 fermatLastTheoremThree

/-- Base case `n = 4`: `x ^ 4 + y ^ 4 = z ^ 4` has no positive solution. -/
