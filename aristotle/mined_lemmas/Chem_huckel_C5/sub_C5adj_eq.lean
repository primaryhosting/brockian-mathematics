import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` on vertices `0,1,2,3,4`:
vertices `i` and `j` are adjacent iff `j ≡ i + 1` or `i ≡ j + 1` modulo `5`. -/

lemma sub_C5adj_eq (m : ℂ) :
    m • (1 : Matrix (Fin 5) (Fin 5) ℂ) - C5adj =
      !![m, -1, 0, 0, -1;
         -1, m, -1, 0, 0;
         0, -1, m, -1, 0;
         0, 0, -1, m, -1;
         -1, 0, 0, -1, m] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C5adj]

/-- The characteristic determinant of the `C₅` adjacency matrix. -/
