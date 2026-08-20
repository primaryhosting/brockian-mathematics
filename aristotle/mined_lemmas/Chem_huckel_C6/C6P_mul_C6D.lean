/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₆` (the Hückel π-system of benzene) are
`2 cos (2πk/6)` for `k = 0, …, 5`.  This is stated as the factorization of the characteristic
polynomial of the adjacency matrix, so that eigenvalues are counted with multiplicity.

The proof diagonalizes the adjacency matrix explicitly: `A = P D P⁻¹` with `P` the (real)
matrix of eigenvectors and `D = diag(2, 1, 1, -1, -1, -2)`, then uses the Mathlib lemmas
`Matrix.charpoly_units_conj` and `Matrix.charpoly_diagonal`.
-/

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

lemma C6P_mul_C6D : C6P * C6D = C6PD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6P, C6D, C6PD, Matrix.mul_apply, Matrix.diagonal_apply]

