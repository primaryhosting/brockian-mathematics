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

open Matrix

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The coordinates of a vector `x` in the orthonormal eigenbasis of a Hermitian matrix `A`,
obtained by applying the adjoint of the eigenvector unitary of `A` to `x`. -/
noncomputable def eigenCoord (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x

/-- **Hermitian quadratic form in eigencoordinates**: for a Hermitian complex matrix `A`,
the quadratic form `star x ⬝ᵥ A *ᵥ x` equals `∑ i, λ i * ‖(eigenCoord x) i‖ ^ 2`,
where the `λ i` are the eigenvalues of `A` (viewed as complex numbers). -/
theorem quadForm_eq_complex (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ A *ᵥ x
      = ∑ i, (hA.eigenvalues i : ℂ) * (‖eigenCoord hA x i‖ : ℂ) ^ 2 := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set y : n → ℂ := star U *ᵥ x with hy
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  have h1 : ((U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U : Matrix n n ℂ)) *ᵥ x
      = U *ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    simp [hy, ← mulVec_mulVec]
  rw [h1, dotProduct_mulVec]
  have h2 : star x ᵥ* U = star y := by
    rw [hy, Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose, star_star]
  rw [h2]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def, Function.comp_apply,
    eigenCoord, ← hU, ← hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, mul_comm (starRingEnd ℂ (y i)), mul_assoc, RCLike.conj_mul]
  norm_cast

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

