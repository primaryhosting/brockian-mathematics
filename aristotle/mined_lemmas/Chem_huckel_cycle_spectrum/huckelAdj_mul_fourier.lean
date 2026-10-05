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

lemma huckelAdj_mul_fourier (hn : 3 ≤ n) :
    huckelAdj n * fourierMat n = fourierMat n * huckelDiag n := by
  ext i k
  have hvec := congrFun (huckelAdj_mulVec hn k) i
  simp only [Matrix.mulVec, dotProduct] at hvec
  rw [Matrix.mul_apply, huckelDiag, Matrix.mul_diagonal, fourierMat, Matrix.vandermonde_apply]
  have hcomm : ∀ j : Fin n, ((omegaC n) ^ j.val) ^ k.val = (omegaC n) ^ (k.val * j.val) := by
    intro j; rw [← pow_mul, mul_comm]
  simp only [Matrix.vandermonde_apply, hcomm]
  rw [hvec]
  ring

end

/-- **Hückel spectrum of the cycle graph.**
For `n ≥ 3`, the spectrum of the adjacency (Hückel) matrix of the cycle graph `C n` is exactly
`{2 cos (2 π k / n) : k = 0, …, n - 1}`. -/
