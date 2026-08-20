import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma adjMatrix_cycleGraph_mulVec (v : Fin 7 → ℂ) (i : Fin 7) :
    ((SimpleGraph.cycleGraph 7).adjMatrix ℂ *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hne : ∀ i : Fin 7, i - 1 ≠ i + 1 := by decide
  have hnb : (SimpleGraph.cycleGraph 7).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 5) (v := i)
  rw [hnb, Finset.sum_pair (hne i)]

/-- The eigenvector attached to `k`. -/
