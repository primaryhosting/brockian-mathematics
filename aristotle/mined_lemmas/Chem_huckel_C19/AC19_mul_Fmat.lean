/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem AC19_mul_Fmat : AC19 * Fmat = Fmat * Matrix.diagonal mu := by
  ext i k
  have h := congrFun (adjMatrix_mulVec_ee k) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simpa [Fmat, mul_comm] using h

/-- **Hückel theory for the cycle `C₁₉`**: the eigenvalues (spectrum) of the adjacency
matrix of the cycle graph on 19 vertices are exactly `2 cos (2πk/19)` for `k = 0, …, 18`. -/
