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

theorem FLT_four : FLTFor 4 := (FLTFor_iff_fermatLastTheoremFor 4).2 fermatLastTheoremFour

/-- **Fermat's Last Theorem: statement and reduction to prime exponents `p ≥ 5`.**

The equation `x ^ n + y ^ n = z ^ n` has no solution in positive integers for any `n > 2`,
provided it has none for prime exponents `p ≥ 5`.

The exponents `n = 3` and `n = 4` (and hence all their multiples) are handled unconditionally
here, using the classical proofs of those two cases; every remaining exponent `n > 2` is
divisible by `4` or by an odd prime, and an odd prime other than `3` is at least `5`. -/
