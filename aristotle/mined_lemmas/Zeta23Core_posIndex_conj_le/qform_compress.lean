/-
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`
(for Hermitian `Q` the value `xᴴ Q x` is real, and `qform` records its real part). -/

theorem qform_compress {m d : Type*} [Fintype m] [Fintype d] (Q : Matrix m m 𝕜)
    (B : Matrix m d 𝕜) (y : d → 𝕜) : qform (Bᴴ * Q * B) y = qform Q (B *ᵥ y) := by
  unfold qform
  congr 1
  simp [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]

/-- The quadratic form of a real diagonal matrix. -/
