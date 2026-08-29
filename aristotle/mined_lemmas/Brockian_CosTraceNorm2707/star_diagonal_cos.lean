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

private theorem star_diagonal_cos (hA : A.IsHermitian) :
    star (diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)))
      = diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  simp only [Matrix.diagonal_eq_diagonal_iff, Function.comp_apply, RCLike.star_def]
  exact fun i => by rw [← Complex.ofReal_cos, Complex.conj_ofReal]

/-- `cos A` is again Hermitian. -/
