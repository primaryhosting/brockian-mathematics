/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with positive integers:
`x ^ n + y ^ n = z ^ n` has no solution with `x, y, z > 0`. -/

theorem FLT_iff_fermatLastTheorem : FLT ↔ FermatLastTheorem := by
  constructor
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).1 (h n (by omega))
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).2 (h n (by omega))

/-- Base case `n = 3` (Euler): from Mathlib's `fermatLastTheoremThree`. -/
