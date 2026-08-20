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

open Matrix

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form attached to a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

theorem qf_conj {m d : Type*} [Fintype m] [Fintype d] (Q : Matrix m m 𝕜) (B : Matrix m d 𝕜)
    (y : d → 𝕜) : qf Q (B *ᵥ y) = qf (Bᴴ * Q * B) y := by
  unfold qf
  rw [Matrix.mul_assoc]
  simp [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]

/-- The quadratic form of a real diagonal matrix. -/
