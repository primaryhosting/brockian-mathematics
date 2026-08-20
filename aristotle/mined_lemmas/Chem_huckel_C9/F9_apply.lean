/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for `C₉`

The Hückel matrix of the cycle `C₉` (in units where the Coulomb integral is `0` and the
resonance integral is `1`) is the adjacency matrix of `SimpleGraph.cycleGraph 9`.
This file diagonalizes it by the discrete Fourier transform (a Vandermonde matrix built from
a primitive ninth root of unity) and computes its characteristic polynomial and spectrum:
the eigenvalues are `2 cos (2πk/9)`, `k = 0, …, 8`.
-/

open Matrix Polynomial SimpleGraph

namespace Chem

/-- A primitive ninth root of unity. -/

lemma F9_apply (i j : Fin 9) : F9 i j = zeta ^ ((i : ℕ) * (j : ℕ)) := by
  simp [F9, Matrix.vandermonde, pow_mul]

