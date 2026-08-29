import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [Fintype d]

/-- The real quadratic form associated with a matrix: `x ↦ re (xᴴ Q x)`. -/

lemma conjTranspose_mulVec_eigenvectorUnitary_mulVec [DecidableEq m] {Q : Matrix m m 𝕜}
    (hQ : Q.IsHermitian) (y : m → 𝕜) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ y)
      = y := by
  rw [Matrix.mulVec_mulVec]
  have h : (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * (hQ.eigenvectorUnitary : Matrix m m 𝕜) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mul_self_of_mem hQ.eigenvectorUnitary.2
  rw [h, Matrix.one_mulVec]

/-- Diagonalization of the quadratic form of a Hermitian matrix. -/
