/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/

lemma C4Adj_eq : C4Adj = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C4Adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj] <;> decide

/-! ### The four Hückel eigenvalues -/

