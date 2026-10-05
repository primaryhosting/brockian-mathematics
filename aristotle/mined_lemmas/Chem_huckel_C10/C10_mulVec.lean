/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma C10_mulVec (v : Fin 10 → ℂ) (i : Fin 10) : (C10 *ᵥ v) i = v (i - 1) + v (i + 1) := by
  fin_cases i <;>
    simp +decide [C10, SimpleGraph.adjMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      SimpleGraph.cycleGraph_adj, show (-1 : Fin 10) = 9 from by decide] <;> ring

