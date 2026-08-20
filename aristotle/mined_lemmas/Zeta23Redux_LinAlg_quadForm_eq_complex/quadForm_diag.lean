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
