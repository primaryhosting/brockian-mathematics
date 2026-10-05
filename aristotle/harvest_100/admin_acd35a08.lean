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
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

/-- The coordinates of a vector `x` in the eigenbasis of a Hermitian matrix `A`:
`eigencoord hA x = U⋆ x`, where `U` is the unitary matrix whose columns are the
eigenvectors of `A`. -/
noncomputable def eigencoord {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x

/-- **Hermitian quadratic form in eigencoordinates.** For a Hermitian matrix `A`,
`star x ⬝ᵥ A *ᵥ x = ∑ i, λᵢ(A) * ‖(eigencoord hA x) i‖ ^ 2`, as an identity of complex
numbers. This is the spectral-decomposition step. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x
      = ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set y : n → ℂ := eigencoord hA x with hy
  have hys : star y = star x ᵥ* U := by
    rw [hy, eigencoord, star_mulVec]
    simp [hU, star_eq_conjTranspose]
  have hA' : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  calc star x ⬝ᵥ A *ᵥ x
      = star x ⬝ᵥ (U *ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (star U *ᵥ x))) := by
        rw [mulVec_mulVec, mulVec_mulVec, ← hA']
    _ = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
        rw [dotProduct_mulVec, hys, hy, eigencoord]
    _ = ∑ i, (hA.eigenvalues i : ℂ) * ((‖y i‖ ^ 2 : ℝ) : ℂ) := by
        rw [dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mulVec_diagonal]
        have hz : (starRingEnd ℂ) (y i) * y i = ((‖y i‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm, Complex.mul_conj]
          norm_cast
          simp [Complex.normSq_eq_norm_sq]
        simp only [Pi.star_apply, RCLike.star_def, Function.comp_apply]
        rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (y i)), mul_assoc, hz]
        simp

end Zeta23Redux.LinAlg

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

