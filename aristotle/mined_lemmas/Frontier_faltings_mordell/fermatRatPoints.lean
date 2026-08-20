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

def fermatRatPoints (n : ℕ) : Set (ℚ × ℚ) := {p : ℚ × ℚ | p.1 ^ n + p.2 ^ n = 1}

/-- The genus of a smooth plane projective curve of degree `n`, given by the degree–genus
formula `g = (n - 1)(n - 2) / 2`.  For the Fermat curve of degree `n` this is its genus. -/
