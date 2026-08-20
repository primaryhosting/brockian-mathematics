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

theorem huckel_C9_charpoly : A9.charpoly = ∏ k : Fin 9, (X - C (lam k)) := by
  have hu : IsUnit F9.det := isUnit_iff_ne_zero.mpr F9_det_ne_zero
  have hinv : F9⁻¹ * F9 = 1 := Matrix.nonsing_inv_mul _ hu
  have hA : A9 = F9 * (Matrix.diagonal lam * F9⁻¹) := by
    rw [← mul_assoc, ← A9_mul_F9, mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one]
  rw [hA, Matrix.charpoly_mul_comm, mul_assoc, hinv, mul_one, Matrix.charpoly_diagonal]

/-- **Hückel theory for `C₉`**: the adjacency (Hückel) eigenvalues of the cycle graph `C₉`
are exactly the numbers `2 cos (2πk/9)` for `k = 0, …, 8`. -/
