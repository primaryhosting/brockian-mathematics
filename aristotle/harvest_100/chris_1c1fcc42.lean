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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Matrix

namespace Zeta23Redux.LinAlg

/-- The eigencoordinates of a vector `x` with respect to the (unitary) eigenvector basis of a
Hermitian matrix `A`: the components of `x` in the orthonormal eigenbasis, i.e. `Uᴴ *ᵥ x` where
`U` is the unitary matrix of eigenvectors from the spectral theorem. -/
noncomputable def eigenCoord {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ x

/-- Conjugating a matrix by a unitary transforms the quadratic form into the quadratic form of
the conjugated matrix evaluated at the transformed vector. -/
private theorem quad_conj {n : Type*} [Fintype n] [DecidableEq n] (U D : Matrix n n ℂ)
    (x : n → ℂ) :
    star x ⬝ᵥ (U * D * Uᴴ) *ᵥ x = star (Uᴴ *ᵥ x) ⬝ᵥ (D *ᵥ (Uᴴ *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- The quadratic form of a real diagonal matrix is the weighted sum of squared norms. -/
private theorem quad_diagonal {n : Type*} [Fintype n] [DecidableEq n] (lam : n → ℝ) (y : n → ℂ) :
    star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ lam) *ᵥ y)
      = ∑ i, (lam i : ℂ) * ((‖y i‖ : ℝ) : ℂ) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (starRingEnd ℂ) (y i) * (y i) = ((‖y i‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.conj_mul']
  rw [show star (y i) = (starRingEnd ℂ) (y i) from rfl]
  rw [show ((RCLike.ofReal (lam i) : ℂ)) = ((lam i : ℝ) : ℂ) from rfl]
  calc (starRingEnd ℂ) (y i) * ((lam i : ℂ) * y i)
      = ((starRingEnd ℂ) (y i) * y i) * (lam i : ℂ) := by ring
    _ = (lam i : ℂ) * ((‖y i‖ : ℝ) : ℂ) ^ 2 := by rw [h]; ring

/-- **Hermitian quadratic form in eigencoordinates.**  For a Hermitian complex matrix `A`,
the quadratic form `star x ⬝ᵥ A *ᵥ x` equals `∑ i, λ i * ‖(eigenCoord x) i‖ ^ 2`, where the
`λ i` are the (real) eigenvalues of `A` and `eigenCoord x` are the coordinates of `x` in the
orthonormal eigenbasis.  This is the spectral-decomposition step. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x
      = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) * ((‖eigenCoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
  have hspec : A = (hA.eigenvectorUnitary : Matrix n n ℂ)
      * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using hA.spectral_theorem
  have h := quad_conj (hA.eigenvectorUnitary : Matrix n n ℂ)
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) x
  rw [← hspec] at h
  rw [h, quad_diagonal]
  rfl

end Zeta23Redux.LinAlg

#print axioms Zeta23Redux.LinAlg.quadForm_eq_complex

