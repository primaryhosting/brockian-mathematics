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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Core

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- The real quadratic form `x ↦ xᴴ Q x` attached to a matrix `Q`. -/

noncomputable def mulVecEquiv {A A' : Matrix m m 𝕜} (h₁ : A * A' = 1) (h₂ : A' * A = 1) :
    (m → 𝕜) ≃ₗ[𝕜] (m → 𝕜) :=
  LinearEquiv.ofLinear A.mulVecLin A'.mulVecLin
    (LinearMap.ext fun x => by simp [Matrix.mulVecLin, Matrix.mulVec_mulVec, h₁])
    (LinearMap.ext fun x => by simp [Matrix.mulVecLin, Matrix.mulVec_mulVec, h₂])

