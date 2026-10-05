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

lemma dftMat_det_ne_zero : dftMat.det ≠ 0 := by
  rw [dftMat, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have := isPrimitiveRoot_zeta17.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

/-- **Hückel theory for the annulene `C₁₇`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₇` factors as `∏ (X - 2cos(2πk/17))`, i.e. the adjacency
eigenvalues of `C₁₇` are exactly `2·cos(2πk/17)` for `k = 0, …, 16`. -/
