/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma adj_mulVec (v : Fin 20 → ℂ) (i : Fin 20) :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : ∀ i : Fin 20, (i - 1 : Fin 20) ≠ i + 1 := by decide
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (hne i)]

