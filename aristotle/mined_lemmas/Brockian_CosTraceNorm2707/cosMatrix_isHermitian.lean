import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

open Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

/-- The matrix `cos A` for a Hermitian matrix `A`, defined through the spectral theorem
(`Matrix.IsHermitian.spectral_theorem`): conjugate the diagonal matrix of the cosines of the
eigenvalues of `A` by the unitary matrix of eigenvectors of `A`. -/

theorem cosMatrix_isHermitian (hA : A.IsHermitian) : (cosMatrix hA).IsHermitian := by
  rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, cosMatrix, ← map_star,
    star_diagonal_cos hA]

/-- Unfolded form of `cosMatrix`: it is the conjugation `U * diag(cos λ) * U*`. -/
