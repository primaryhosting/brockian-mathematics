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

lemma sub_one_ne_add_one (x : Fin 14) : x - 1 ≠ x + 1 := by
  revert x; decide

/-- The adjacency matrix is diagonalised by the DFT matrix: `A * F = F * D`. -/
