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

lemma F9_det_ne_zero : F9.det ≠ 0 := by
  rw [F9, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (zeta_primitive.pow_inj a.isLt b.isLt hab)

/-- The characteristic polynomial of the Hückel matrix of `C₉` factors with roots
`2 cos (2πk/9)`. -/
