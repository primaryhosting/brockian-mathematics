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

lemma ch_eq_exp (k : ZMod 13) :
    ch k = Complex.exp (((2 * Real.pi * k.val / 13 : ℝ) : ℂ) * Complex.I) := by
  rw [ch, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

