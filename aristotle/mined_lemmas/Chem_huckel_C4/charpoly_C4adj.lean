/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene
with `α = 0`, `β = 1`), viewed over `ℂ`. -/

lemma charpoly_C4adj : C4adj.charpoly = X ^ 4 - 4 * X ^ 2 := by
  rw [Matrix.charpoly, charmatrix_C4adj]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **Hückel theory for cyclobutadiene (the cycle graph `C₄`).**

The eigenvalues of the adjacency matrix of `C₄` are exactly the numbers `2 cos (2πk/4)`
for `k = 0, 1, 2, 3`, and each of these numbers is indeed an eigenvalue, witnessed by an
explicit nonzero eigenvector. -/
