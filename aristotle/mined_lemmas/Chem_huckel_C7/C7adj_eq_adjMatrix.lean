/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of a 7-membered
ring, in units where α = 0 and β = 1): the vertices are `Fin 7` and `i` is adjacent to
`i + 1` and `i - 1`, the arithmetic being modulo 7. -/

lemma C7adj_eq_adjMatrix : C7adj = (SimpleGraph.cycleGraph 7).adjMatrix ℂ := by
  ext i j
  simp only [C7adj, Matrix.of_apply, SimpleGraph.adjMatrix_apply, cycleGraph_seven_adj]

/-- The basic 7th root of unity `exp (2πi/7)`. -/
