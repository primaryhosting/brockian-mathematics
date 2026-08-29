import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
In Hückel molecular orbital theory the π-energies of an annulene `C_n H_n` are `α + β λ`,
where `λ` runs over the eigenvalues of the adjacency matrix of the cycle graph `C n`.
This file proves that this spectrum is exactly `{2 cos (2 π k / n) : k = 0, …, n-1}`.

The proof diagonalizes the (circulant) adjacency matrix by the Vandermonde/Fourier matrix
built from the `n`-th roots of unity.
-/

open scoped BigOperators Real

namespace Chem

open SimpleGraph Matrix Complex

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with entries in `ℂ`:
the `(i, j)` entry is `1` when `i` and `j` are adjacent in `C n`, and `0` otherwise. -/

lemma fourierMat_det_ne_zero (hn : 3 ≤ n) : (fourierMat n).det ≠ 0 := by
  have hn0 : n ≠ 0 := by omega
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext ((Complex.isPrimitiveRoot_exp n hn0).pow_inj i.isLt j.isLt hij)

