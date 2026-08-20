/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the header
-- above is a plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- The primitive 13-th root of unity `exp(2πi/13)`. -/

lemma ch_ne_zero (x : ZMod 13) : ch x ≠ 0 := by
  have h : om ≠ 0 := Complex.exp_ne_zero _
  simp [ch, h]

