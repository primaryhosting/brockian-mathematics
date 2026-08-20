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

lemma cycleGraph_seven_adj (i j : Fin 7) :
    (SimpleGraph.cycleGraph 7).Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  have h := @SimpleGraph.cycleGraph_adj 5 i j
  rw [h]
  clear h
  revert i j
  decide

/-- `C7adj` really is the adjacency matrix of the cycle graph `C₇`. -/
