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

lemma C6adj_charpoly :
    C6adj.charpoly = ∏ i : Fin 6, (X - C (![(2:ℝ), 1, 1, -1, -1, -2] i)) := by
  rw [C6adj_conj]
  have h : C6P * C6D * C6Q = (C6Punit : Matrix (Fin 6) (Fin 6) ℝ) * C6D *
      ((C6Punit⁻¹ : (Matrix (Fin 6) (Fin 6) ℝ)ˣ) : Matrix (Fin 6) (Fin 6) ℝ) := rfl
  rw [h, Matrix.charpoly_units_conj, C6D, Matrix.charpoly_diagonal]

/-- The six numbers `2 cos (2πk/6)`, `k = 0, …, 5`, are `2, 1, -1, -2, -1, 1`. -/
