import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/

lemma cycleGraph9_mulVec (v : Fin 9 → ℂ) (i : Fin 9) :
    ((cycleGraph 9).adjMatrix ℂ *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply,
    show (cycleGraph 9).neighborFinset i = {i - 1, i + 1} from cycleGraph_neighborFinset (n := 7),
    Finset.sum_pair (by revert i; decide)]

/-- If `W ^ 9 = 1` then `j ↦ W ^ j` satisfies the eigenvector recurrence with
eigenvalue `W + W ^ 8`. -/
