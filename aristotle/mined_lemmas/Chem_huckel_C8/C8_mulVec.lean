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
-/

open Real Matrix SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₈`, i.e. the Hückel matrix of
cyclooctatetraene in units where `α = 0` and `β = 1`. -/

lemma C8_mulVec (v : Fin 8 → ℝ) (i : Fin 8) : (C8 *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [C8, SimpleGraph.adjMatrix_mulVec_apply]
  have h : (SimpleGraph.cycleGraph 8).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 6) (v := i)
  rw [h, Finset.sum_pair]
  revert i
  decide

/-- The angle `2πk/8`. -/
