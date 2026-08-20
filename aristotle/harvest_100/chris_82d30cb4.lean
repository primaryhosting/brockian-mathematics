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
i.e. `Uᴴ x` where `U` is the unitary matrix whose columns are the eigenvectors of `A`. -/
noncomputable def eigencoord {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  (star (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ x

/-- **Hermitian quadratic form in eigencoordinates.** For a Hermitian matrix `A`, the quadratic
form `x ↦ xᴴ A x` equals `∑ i, λ i * ‖(eigencoord x) i‖ ^ 2`, where the `λ i` are the eigenvalues
of `A`. -/
theorem quadForm_eq_complex {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x
      = ∑ i, (hA.eigenvalues i : ℂ) * ((‖eigencoord hA x i‖ : ℂ)) ^ 2 := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  set y : n → ℂ := eigencoord hA x with hy
  have hAeq : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hU, hD, Unitary.conjStarAlgAut_apply]
  have hmul : A *ᵥ x = U *ᵥ (D *ᵥ y) := by
    rw [hAeq, hy, eigencoord, mulVec_mulVec, mulVec_mulVec]
  have hstar : star x ᵥ* U = star y := by
    rw [hy, eigencoord, star_mulVec]
    simp [hU, Matrix.star_eq_conjTranspose]
  rw [hmul, dotProduct_mulVec, hstar]
  simp only [dotProduct, hD, mulVec_diagonal, Pi.star_apply, RCLike.star_def,
    Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (starRingEnd ℂ) (y i) * (y i) = ((‖y i‖ : ℂ)) ^ 2 := by
    rw [Complex.conj_mul']
  rw [show RCLike.ofReal (hA.eigenvalues i) * y i = ((hA.eigenvalues i : ℂ)) * y i from rfl,
    ← mul_assoc, mul_comm ((starRingEnd ℂ) (y i)), mul_assoc, this]

end Zeta23Redux.LinAlg

