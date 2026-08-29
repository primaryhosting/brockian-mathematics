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

theorem FLT_iff_fermatLastTheorem : FLT ↔ FermatLastTheorem := by
  constructor
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).1 (h n (by omega))
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).2 (h n (by omega))

/-- If `FLTFor` holds for an exponent `m`, it holds for every multiple of `m`. -/
