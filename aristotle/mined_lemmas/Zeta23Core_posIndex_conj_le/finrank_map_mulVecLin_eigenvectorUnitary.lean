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

lemma finrank_map_mulVecLin_eigenvectorUnitary (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian)
    (p : Submodule 𝕜 (m → 𝕜)) :
    Module.finrank 𝕜 (Submodule.map
        (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) p)
      = Module.finrank 𝕜 p := by
  have hc1 : (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) ∘ₗ
      (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ) = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, eigenvectorUnitary_mul_conjTranspose Q hQ, Matrix.mulVecLin_one]
  have hc2 : (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ) ∘ₗ
      (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, conjTranspose_mul_eigenvectorUnitary Q hQ, Matrix.mulVecLin_one]
  have key := LinearEquiv.finrank_map_eq
    (LinearEquiv.ofLinear (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜))
      (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ) hc1 hc2) p
  simpa using key

/-- There is a subspace of dimension `posIndex Q` on which `Q` is positive definite. -/
