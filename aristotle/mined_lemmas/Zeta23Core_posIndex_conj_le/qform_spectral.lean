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

lemma qform_spectral {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (y : m → 𝕜) :
    qform Q ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ y)
      = qform (Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) : Matrix m m 𝕜) y := by
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  set D : Matrix m m 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues) with hD
  have hspec : Q = U * D * star U := hQ.spectral_theorem
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hQ.eigenvectorUnitary
  have hQU : Q * U = U * D := by rw [hspec, mul_assoc, mul_assoc, hUU, mul_one]
  unfold qform
  congr 1
  rw [Matrix.mulVec_mulVec, hQU, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec, Matrix.vecMul_vecMul]
  have hUh : Uᴴ * U = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact hUU
  rw [hUh, Matrix.vecMul_one]

