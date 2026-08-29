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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The coordinates of a vector `x` in the orthonormal eigenbasis of a Hermitian matrix `A`,
i.e. `x` expressed against the columns of the unitary eigenvector matrix of `A`. -/
noncomputable def eigencoord {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  (star (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ x

/-- Spectral decomposition of a Hermitian matrix, in the explicit form `A = U D Uᴴ`. -/
theorem hermitian_eq_conj_diagonal {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]

/-- **Hermitian quadratic form in eigencoordinates.**  For a Hermitian complex matrix `A`,
the quadratic form `star x ⬝ᵥ A *ᵥ x` equals `∑ i, λ i * ‖(eigencoord x) i‖ ^ 2`, where the
`λ i` are the eigenvalues of `A` and `eigencoord x` are the coordinates of `x` in the
eigenbasis. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x
      = ∑ i, (hA.eigenvalues i : ℂ) * (‖eigencoord hA x i‖ : ℂ) ^ 2 := by
  classical
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  obtain ⟨y, hy⟩ : ∃ y : n → ℂ, y = star U *ᵥ x := ⟨_, rfl⟩
  have hey : eigencoord hA x = y := by rw [hy, eigencoord, hU]
  rw [hey]
  have hA' : A = U * D * star U := hermitian_eq_conj_diagonal hA
  have e1 : star y = star x ᵥ* U := by
    rw [hy, Matrix.star_mulVec]
    simp
  have h1 : star x ⬝ᵥ A *ᵥ x = star y ⬝ᵥ (D *ᵥ y) := by
    rw [hA', e1, hy, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [h1, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.star_apply, Matrix.mulVec_diagonal, hD, Function.comp_apply]
  rw [show star (y i) * ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * y i)
      = (RCLike.ofReal (hA.eigenvalues i) : ℂ) * (star (y i) * y i) by ring]
  rw [show (star (y i) * y i) = (starRingEnd ℂ) (y i) * y i from rfl, Complex.conj_mul']
  simp

end Zeta23Redux.LinAlg

