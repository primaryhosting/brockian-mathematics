/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix SimpleGraph

namespace Chem

/-- The primitive 13-th root of unity `exp (2πi/13)`. -/

lemma xi_zero : xi 0 = 1 := by simp [xi]

