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

theorem mulVec_huckelEigenvector (k : Fin 15) :
    C15adj.mulVec (huckelEigenvector k) = huckelEigenvalue k • huckelEigenvector k := by
  funext i
  rw [C15adj_mulVec]
  simp only [huckelEigenvector, Pi.smul_apply, smul_eq_mul, huckelEigenvalue_eq]
  rw [zeta_pow_succ, zeta_pow_pred]
  ring

/-! ### Diagonalization by the discrete Fourier matrix -/

/-- The (unnormalized) discrete Fourier matrix: its `k`-th column is `huckelEigenvector k`. -/
