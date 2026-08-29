/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₉`

We show that the spectrum of the adjacency matrix of the cycle graph `C₁₉`
(the Hückel matrix of the annulene `C₁₉` in units where `α = 0`, `β = 1`)
is exactly `{2 cos (2πk/19) : k = 0, …, 18}`.

The proof diagonalizes the circulant adjacency matrix by the discrete Fourier matrix.
-/

namespace Chem

open Complex Matrix Finset

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- A primitive 19-th root of unity. -/

lemma det_diagonal_charpoly_factors :
    (diagonal (fun k : ZMod 19 => Polynomial.X - Polynomial.C (mu k))).det
      = ∏ k : ZMod 19, (Polynomial.X - Polynomial.C (mu k)) := by
  rw [Matrix.det_diagonal]

/-- The characteristic polynomial of the adjacency matrix of `C₁₉` factors as
`∏_{k=0}^{18} (X - 2 cos (2πk/19))`; in particular the `19` eigenvalues, counted with
multiplicity, are the numbers `2 cos (2πk/19)`, `k = 0, …, 18`. -/
