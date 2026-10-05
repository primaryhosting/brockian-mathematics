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

theorem adjMatrix_cycleGraph_four :
    ((SimpleGraph.cycleGraph 4).adjMatrix ℝ) = !![(0:ℝ),1,0,1; 1,0,1,0; 0,1,0,1; 1,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.adjMatrix, SimpleGraph.cycleGraph, SimpleGraph.circulantGraph,
      SimpleGraph.fromRel] <;> decide

/-- The characteristic matrix of the adjacency matrix of `C₄`. -/
