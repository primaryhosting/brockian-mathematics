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

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The real quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

lemma eigenvectorUnitary_mulVec_left_inv (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) (x : m → 𝕜) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ
      ((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x) = x := by
  rw [mulVec_mulVec, eigenvectorUnitary_mul_conjTranspose Q hQ, one_mulVec]

/-- Multiplication by a unitary matrix preserves dimensions of subspaces. -/
