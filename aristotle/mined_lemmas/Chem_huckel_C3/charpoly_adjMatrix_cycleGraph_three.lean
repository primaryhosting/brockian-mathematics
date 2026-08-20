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

lemma charpoly_adjMatrix_cycleGraph_three :
    ((SimpleGraph.cycleGraph 3).adjMatrix ℝ).charpoly = X ^ 3 - 3 * X - 2 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [charmatrix_apply, Matrix.diagonal_apply, adjMatrix_cycleGraph_three]
  norm_num [Fin.ext_iff]
  ring

