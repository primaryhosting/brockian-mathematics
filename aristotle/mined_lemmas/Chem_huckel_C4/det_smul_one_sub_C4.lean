import Mathlib
/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Chem

/-- The Hückel (adjacency) matrix of the cycle `C₄`: `A i j = 1` exactly when the carbon
atoms `i` and `j` are neighbours in the four-membered ring. -/

lemma det_smul_one_sub_C4 (mu : ℝ) :
    (mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) - C4).det = mu ^ 4 - 4 * mu ^ 2 := by
  have h : mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) - C4 =
      !![mu, -1, 0, -1; -1, mu, -1, 0; 0, -1, mu, -1; -1, 0, -1, mu] := by
    rw [C4_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  ring

