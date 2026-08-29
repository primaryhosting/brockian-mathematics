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

lemma charpoly_cycleAdj_four : (cycleAdj 4).charpoly = X ^ 4 - 4 * X ^ 2 := by
  have h : Matrix.charmatrix (cycleAdj 4)
      = !![X, -1, 0, -1; -1, X, -1, 0; 0, -1, X, -1; -1, 0, -1, X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycleAdj_four, Matrix.charmatrix]
  rw [Matrix.charpoly, h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The Hückel eigenvalues `2 cos (2πk/4)`, `k = 0,1,2,3`, are `2, 0, -2, 0`. -/
