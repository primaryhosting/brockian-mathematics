import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Chem

/-- Adjacency matrix of the cycle graph `C₃`: every pair of distinct vertices is adjacent. -/

lemma C3adj_mulVec (v : Fin 3 → ℝ) (i : Fin 3) :
    C3adj.mulVec v i = (v 0 + v 1 + v 2) - v i := by
  fin_cases i <;>
    simp [C3adj, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

