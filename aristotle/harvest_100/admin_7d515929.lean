/-
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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
obtained by applying the adjoint of the unitary whose columns are the eigenvectors of `A`. -/
noncomputable def eigencoord {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x

/-- **Hermitian quadratic form in eigencoordinates.**  For a Hermitian complex matrix `A`, the
quadratic form `star x ⬝ᵥ A *ᵥ x` equals `∑ i, λ i * ‖(eigencoord x) i‖ ^ 2`, where the `λ i` are
the (real) eigenvalues of `A` and `eigencoord x` are the coordinates of `x` in the eigenbasis. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hAeq : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hU, hD, Unitary.conjStarAlgAut_apply]
  have hy : eigencoord hA x = star U *ᵥ x := rfl
  have hstar : star (eigencoord hA x) = star x ᵥ* U := by
    rw [hy, star_mulVec]
    simp [hU, Matrix.star_eq_conjTranspose]
  calc star x ⬝ᵥ A *ᵥ x
      = star x ⬝ᵥ (U *ᵥ (D *ᵥ (star U *ᵥ x))) := by
        rw [hAeq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = (star x ᵥ* U) ⬝ᵥ (D *ᵥ eigencoord hA x) := by
        rw [dotProduct_mulVec, hy]
    _ = star (eigencoord hA x) ⬝ᵥ (D *ᵥ eigencoord hA x) := by rw [hstar]
    _ = ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
        simp only [hD, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply,
          Function.comp_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : star (eigencoord hA x i) * eigencoord hA x i
            = ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
          simpa using RCLike.conj_mul (K := ℂ) (eigencoord hA x i)
        calc star (eigencoord hA x i) * ((hA.eigenvalues i : ℂ) * eigencoord hA x i)
            = (hA.eigenvalues i : ℂ) * (star (eigencoord hA x i) * eigencoord hA x i) := by ring
          _ = (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by rw [hc]

end Zeta23Redux.LinAlg

