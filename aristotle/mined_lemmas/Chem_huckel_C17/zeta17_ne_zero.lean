/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/

lemma zeta17_ne_zero : zeta17 ≠ 0 := by
  intro h
  have := zeta17_pow_seventeen
  rw [h] at this
  norm_num at this

/-- The Fourier / Vandermonde matrix `P j k = ζ^(jk)`. -/
