/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Polynomial Real

/-- Adjacency matrix of the cycle graph `C n` on the vertex set `Fin n`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `n`. -/

lemma cycleAdj_four :
    cycleAdj 4 = !![(0 : ℝ), 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycleAdj]

set_option maxHeartbeats 1000000 in
/-- The characteristic polynomial of the adjacency matrix of `C 4`. -/
