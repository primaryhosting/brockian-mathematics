import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₄` (vertices indexed cyclically by `Fin 4`:
`i` is adjacent to `i + 1` and `i - 1`). -/

lemma C4adj_mulVec (v : Fin 4 → ℝ) :
    C4adj *ᵥ v = ![v 1 + v 3, v 0 + v 2, v 1 + v 3, v 0 + v 2] := by
  funext i
  fin_cases i <;>
    simp +decide [C4adj, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The four Hückel expressions `2·cos(2πk/4)`, `k = 0, 1, 2, 3`, are `2, 0, -2, 0`. -/
