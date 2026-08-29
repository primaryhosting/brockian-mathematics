/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency (Hückel) matrix of the cycle graph `C₁₄` is diagonalised by the discrete Fourier
transform on `ZMod 14`; its characteristic polynomial is therefore
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, i.e. its eigenvalues are `2 cos (2πk/14)` for `k = 0, …, 13`.
-/

open Complex Polynomial Matrix

namespace Chem

noncomputable section

/-- A primitive 14-th root of unity. -/

noncomputable def dftUnit : (Matrix (ZMod 14) (ZMod 14) ℂ)ˣ :=
  ⟨dftU, dftV, dftU_mul_dftV, dftV_mul_dftU⟩

/-- The adjacency matrix of `C₁₄` is conjugate to the diagonal matrix of the numbers
`2 cos (2πk/14)`. -/
