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

lemma ch_add_ch_neg (k : ZMod 13) : ch k + ch (-k) = eig k := by
  rw [ch_neg, ch_eq_exp, ← Complex.exp_neg, eig, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

/-- The matrix whose columns are the eigenvectors (a discrete Fourier transform matrix). -/
