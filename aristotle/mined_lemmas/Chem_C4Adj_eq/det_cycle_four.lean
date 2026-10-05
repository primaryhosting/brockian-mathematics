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

lemma det_cycle_four {R : Type*} [CommRing R] (r : R) :
    (!![r, -1, 0, -1; -1, r, -1, 0; 0, -1, r, -1; -1, 0, -1, r] : Matrix (Fin 4) (Fin 4) R).det
      = r ^ 4 - 4 * r ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

