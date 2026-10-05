import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexConjugate

namespace Zeta23Redux.LinAlg

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coordinates of a vector `x` in the eigenbasis of a Hermitian matrix `A`,
i.e. `U* x` where `U` is the unitary whose columns are the eigenvectors of `A`. -/
noncomputable def eigencoord {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  (star (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ x

/-- Hermitian quadratic form in eigencoordinates:
`star x ⬝ᵥ A *ᵥ x = ∑ i, λ i * ‖(eigencoord x) i‖ ^ 2` as a complex number. -/
theorem quadForm_eq_complex {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x =
      ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hAeq : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU]
  have hstar : star (star U *ᵥ x) = star x ᵥ* U := by
    rw [Matrix.star_mulVec]
    simp
  calc star x ⬝ᵥ A *ᵥ x
      = star (eigencoord hA x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *ᵥ
          (eigencoord hA x) := by
        rw [eigencoord, hstar, hAeq]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    _ = ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
        rw [Matrix.dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_diagonal]
        have : (starRingEnd ℂ) (eigencoord hA x i) * eigencoord hA x i =
            ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
          rw [Complex.conj_mul']
          push_cast
          ring
        simp only [Pi.star_apply, RCLike.star_def, Function.comp_apply]
        calc (starRingEnd ℂ) (eigencoord hA x i) *
              ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * eigencoord hA x i)
            = (hA.eigenvalues i : ℂ) *
              ((starRingEnd ℂ) (eigencoord hA x i) * eigencoord hA x i) := by
              simp [RCLike.ofReal_alg]; ring
          _ = (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℝ) : ℂ) ^ 2 := by rw [this]

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

