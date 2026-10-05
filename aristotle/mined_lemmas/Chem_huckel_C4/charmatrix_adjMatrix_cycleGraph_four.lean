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

theorem charmatrix_adjMatrix_cycleGraph_four :
    Matrix.charmatrix ((SimpleGraph.cycleGraph 4).adjMatrix ℝ) =
      !![X, -1, 0, -1; -1, X, -1, 0; (0:ℝ[X]), -1, X, -1; -1, 0, -1, X] := by
  rw [adjMatrix_cycleGraph_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.charmatrix]

/-- The characteristic polynomial of the adjacency matrix of `C₄` is `X⁴ - 4X²`. -/
