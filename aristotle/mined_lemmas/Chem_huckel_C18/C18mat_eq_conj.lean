/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem C18mat_eq_conj : C18mat = Pmat * Dmat * Qmat := by
  rw [← C18mat_mul_Pmat, mul_assoc, Pmat_mul_Qmat, mul_one]

/-- The eigenvector equation: the vector `j ↦ ζ^{jk}` is an eigenvector of the adjacency
matrix of `C₁₈` with eigenvalue `2 cos (2πk/18)`. -/
