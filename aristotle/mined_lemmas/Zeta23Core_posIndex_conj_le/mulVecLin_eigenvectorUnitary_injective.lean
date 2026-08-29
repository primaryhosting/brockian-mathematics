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

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The (real) quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

lemma mulVecLin_eigenvectorUnitary_injective {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    Function.Injective (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) := by
  intro a b hab
  have h1 : (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *
      (hQ.eigenvectorUnitary : Matrix m m 𝕜) = 1 := Unitary.coe_star_mul_self _
  have h2 : (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *ᵥ
        ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ a)
      = (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *ᵥ
        ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ b) := by
    simpa [Matrix.mulVecLin] using
      congrArg (fun v => (star (hQ.eigenvectorUnitary : Matrix m m 𝕜)) *ᵥ v) hab
  rwa [mulVec_mulVec, mulVec_mulVec, h1, one_mulVec, one_mulVec] at h2

/-- The span of the eigenvectors indexed by `s`. -/
