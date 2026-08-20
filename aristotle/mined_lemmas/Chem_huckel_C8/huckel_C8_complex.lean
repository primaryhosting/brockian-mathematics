/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₈` (the Hückel π-system of cyclooctatetraene)
are `2 cos (2πk/8)` for `k = 0, …, 7`.  This is expressed as a complete factorisation of the
characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 8`.

The proof diagonalises the adjacency matrix by the discrete Fourier matrix built from the
primitive eighth root of unity `ω = (√2/2)(1 + i)`.
-/

open Matrix Complex Polynomial SimpleGraph

namespace Chem

/-- The primitive eighth root of unity `exp (2πi/8) = (√2/2)(1 + i)`. -/

theorem huckel_C8_complex :
    ((cycleGraph 8).adjMatrix ℂ).charpoly =
      ∏ k : Fin 8, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 8) : ℝ) : ℂ)) := by
  rw [charpoly_adj_complex, eigDiag, Matrix.charpoly_diagonal]
  exact Finset.prod_congr rfl fun k _ => by rw [eig_entry k.val k.isLt]

