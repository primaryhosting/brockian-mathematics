/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/

lemma resolvent_matrix (r : ℂ) :
    r • (1 : Matrix (Fin 4) (Fin 4) ℂ) - C4Adj =
      !![r, -1, 0, -1; -1, r, -1, 0; 0, -1, r, -1; -1, 0, -1, r] := by
  rw [C4Adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The spectrum of the adjacency matrix of `C₄` is `{2, 0, -2}`. -/
