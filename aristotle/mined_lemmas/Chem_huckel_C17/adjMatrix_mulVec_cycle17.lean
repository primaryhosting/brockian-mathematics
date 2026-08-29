/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/

lemma adjMatrix_mulVec_cycle17 (v : Fin 17 → ℂ) (j : Fin 17) :
    ((cycleGraph 17).adjMatrix ℂ *ᵥ v) j = v (j - 1) + v (j + 1) := by
  have hne : ∀ x : Fin 17, x - 1 ≠ x + 1 := by decide
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (hne j)]

/-- The diagonalization identity `A · P = P · D`. -/
