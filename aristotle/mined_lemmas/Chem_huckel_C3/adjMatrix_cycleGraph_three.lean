/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real Matrix SimpleGraph

namespace Chem

/-- The Hückel level of the `k`-th molecular orbital of the cyclic `C₃` system,
in units of the resonance integral `β` (relative to `α`): `2 cos (2πk/3)`. -/

lemma adjMatrix_cycleGraph_three (i j : Fin 3) :
    (SimpleGraph.cycleGraph 3).adjMatrix ℝ i j = if i = j then 0 else 1 := by
  rw [SimpleGraph.adjMatrix_apply]
  rcases eq_or_ne i j with h | h
  · simp [h]
  · have : (SimpleGraph.cycleGraph 3).Adj i j := by
      rw [SimpleGraph.cycleGraph_three_eq_top]
      exact h
    simp [this, h]

/-- The characteristic polynomial of the adjacency matrix of `C₃` is `X³ - 3X - 2`. -/
