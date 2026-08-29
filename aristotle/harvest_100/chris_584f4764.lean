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

namespace Zeta23Redux.LinAlg

open Matrix

/-- The coordinates of a vector `x` in the orthonormal eigenbasis of a Hermitian matrix `A`,
i.e. `U⋆ x` where `U` is the unitary whose columns are the eigenvectors of `A`. -/
noncomputable def eigencoord {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x

/-- Hermitian quadratic form in eigencoordinates: for a Hermitian complex matrix `A`,
`x⋆ A x = ∑ᵢ λᵢ(A) ‖(U⋆ x)ᵢ‖²` as a complex number. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      ∑ i, (hA.eigenvalues i : ℂ) * (‖eigencoord hA x i‖ : ℂ) ^ 2 := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set y : n → ℂ := star U *ᵥ x with hy
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hyc : ∀ i, eigencoord hA x i = y i := fun _ => rfl
  have hA' : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hD]
  have hAx : A *ᵥ x = U *ᵥ (D *ᵥ y) := by
    conv_lhs => rw [hA']
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hxy : star x ᵥ* U = star y := by
    rw [hy, Matrix.star_mulVec]
    simp [hU, Matrix.star_eq_conjTranspose]
  rw [hAx, Matrix.dotProduct_mulVec, hxy, hD, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hyc, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def, Function.comp_apply]
  have h : (starRingEnd ℂ) (y i) * y i = ((‖y i‖ : ℂ)) ^ 2 := by
    rw [mul_comm, Complex.mul_conj']
  have hcast : (RCLike.ofReal (hA.eigenvalues i) : ℂ) = ((hA.eigenvalues i : ℝ) : ℂ) := rfl
  rw [hcast]
  linear_combination (hA.eigenvalues i : ℂ) * h

end Zeta23Redux.LinAlg

