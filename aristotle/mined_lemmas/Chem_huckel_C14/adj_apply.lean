import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma adj_apply (j i : Fin 14) :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) j i = if i = j - 1 ∨ i = j + 1 then 1 else 0 := by
  rw [SimpleGraph.adjMatrix_apply]
  simp only [cycle_adj_iff]

