/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15

Category: Chemistry.  Target: `Chem.huckel_C15`.

The Hückel (adjacency) eigenvalues of the cycle graph `C₁₅` are `2 cos (2πk/15)`, `k = 0, …, 14`.

The proof diagonalizes the adjacency matrix by the discrete Fourier matrix
`U i k = ζ ^ (k * i)` with `ζ = exp (2πi/15)`, and then uses
`spectrum.units_conjugate` together with `spectrum_diagonal`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/

theorem C15adj_mul_dftMatrix :
    C15adj * dftMatrix = dftMatrix * Matrix.diagonal huckelEigenvalue := by
  ext i k
  have hleft : (C15adj * dftMatrix) i k = C15adj.mulVec (huckelEigenvector k) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, dftMatrix, huckelEigenvector]
  rw [hleft, mulVec_huckelEigenvector, Matrix.mul_apply]
  simp [Matrix.diagonal, Pi.smul_apply, dftMatrix, huckelEigenvector, Finset.sum_ite_eq',
    mul_comm]

/-! ### The main theorem -/

/-- The adjacency (Hückel) spectrum of the cycle graph `C₁₅` consists exactly of the numbers
`2 cos (2πk/15)` for `k = 0, …, 14`. -/
