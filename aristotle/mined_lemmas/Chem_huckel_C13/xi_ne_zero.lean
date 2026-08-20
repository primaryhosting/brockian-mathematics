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

lemma xi_ne_zero (a : Fin 13) : xi a ≠ 0 := by
  simp [xi, zeta13, Complex.exp_ne_zero]

