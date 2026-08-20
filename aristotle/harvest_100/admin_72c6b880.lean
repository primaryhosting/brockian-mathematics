/-
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux
namespace LinAlg

/-- The coordinates of a vector `x` in the orthonormal eigenbasis of a Hermitian matrix `A`,
i.e. `U⋆ x` where `U` is the unitary whose columns are the eigenvectors of `A`. -/
noncomputable def eigencoord {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  (star (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ x

/-- Unitary diagonalization of a Hermitian matrix, in the form `A = U * D * U⋆`. -/
theorem hermitian_eq_conj {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
        star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- Key intermediate step: in eigencoordinates the Hermitian quadratic form becomes the
quadratic form of the diagonal matrix of eigenvalues. -/
theorem quadForm_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      star (eigencoord hA x) ⬝ᵥ
        (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *ᵥ eigencoord hA x) := by
  have h : star (eigencoord hA x) = star x ᵥ* (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    rw [eigencoord, Matrix.star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  conv_lhs => rw [hermitian_eq_conj hA]
  rw [h, eigencoord, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]

/-- **Hermitian quadratic form in eigencoordinates.** For a Hermitian matrix `A` and any vector
`x`, the (complex) quadratic form `x⋆ A x` equals `∑ᵢ λᵢ(A) · ‖(eigencoord x)ᵢ‖²`. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x = ∑ i, (hA.eigenvalues i : ℂ) * (‖eigencoord hA x i‖ : ℂ) ^ 2 := by
  rw [quadForm_diag hA x, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def]
  rw [show ((‖eigencoord hA x i‖ : ℂ)) ^ 2 =
      (starRingEnd ℂ) (eigencoord hA x i) * eigencoord hA x i from by
    rw [RCLike.conj_mul]; norm_cast]
  ring

end LinAlg
end Zeta23Redux

