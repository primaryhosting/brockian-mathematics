import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma C8adj_sum (i : Fin 8) (f : Fin 8 → ℂ) :
    ∑ l, C8adj i l * f l = f (i + 1) + f (i - 1) := by
  simp only [C8adj]
  fin_cases i <;>
    simp +decide [Fin.sum_univ_eight, show (-1 : Fin 8) = 7 from by decide] <;> ring

/-- The columns of the DFT matrix are eigenvectors of the adjacency matrix, with
eigenvalues `2 cos (2πk/8)`. -/
