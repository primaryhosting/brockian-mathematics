/-
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is kept at the top of the file as a plain block comment:
-- Lean 4 does not allow a module docstring `/-! ... -/` to precede the `import` line.)

import Mathlib

namespace Infinity

/-- The rationals are countable. -/

def ratDenumerable : Denumerable ℚ := inferInstance

/-- The cardinality of the rationals is `ℵ₀`. -/
