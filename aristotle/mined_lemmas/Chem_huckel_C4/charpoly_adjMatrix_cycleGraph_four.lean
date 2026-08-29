/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Polynomial

/-- The adjacency matrix of the cycle graph `C₄` (over `ℝ`), written explicitly. -/

theorem charpoly_adjMatrix_cycleGraph_four :
    ((SimpleGraph.cycleGraph 4).adjMatrix ℝ).charpoly = X ^ 4 - 4 * X ^ 2 := by
  rw [Matrix.charpoly, charmatrix_adjMatrix_cycleGraph_four]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    show ((1 : Fin 3) < 2) from by decide]
  ring

/-- **Hückel theory for cyclobutadiene (C₄).**  The eigenvalues of the adjacency matrix of the
cycle graph `C₄` are exactly `2 cos (2πk/4)` for `k = 0, 1, 2, 3`, with multiplicity:  the
characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/4))`. -/
