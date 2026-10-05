import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma C8adj_eq_adjMatrix : C8adj = (SimpleGraph.cycleGraph 8).adjMatrix ℂ := by
  ext i j
  simp only [C8adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]
  congr 1
  revert i j
  decide

