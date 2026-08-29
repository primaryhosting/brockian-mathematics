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

theorem cosMatrix_eq (hA : A.IsHermitian) :
    cosMatrix hA = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      * (diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)))
      * star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
  Unitary.conjStarAlgAut_apply _ _

/-- The trace of `cos A` is the sum of the cosines of the eigenvalues of `A`. -/
