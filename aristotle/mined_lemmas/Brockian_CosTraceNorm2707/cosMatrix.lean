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

noncomputable def cosMatrix (hA : A.IsHermitian) : Matrix (Fin n) (Fin n) ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ)) hA.eigenvectorUnitary
    (diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)))

/-- The trace norm (Schatten 1-norm) of `cos A`: since `cos A` is Hermitian with eigenvalues
`cos λᵢ`, its singular values are `|cos λᵢ|`. -/
