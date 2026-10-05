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

lemma charmatrix_C4Adj :
    charmatrix C4Adj = !![Polynomial.X, -1, 0, -1; -1, Polynomial.X, -1, 0;
      0, -1, Polynomial.X, -1; -1, 0, -1, Polynomial.X] := by
  rw [C4Adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charmatrix]

/-- The characteristic polynomial of the adjacency matrix of `C₄` factors as
`∏ k, (X - 2 cos (2πk/4))`; in particular the eigenvalue `0` is doubly degenerate. -/
