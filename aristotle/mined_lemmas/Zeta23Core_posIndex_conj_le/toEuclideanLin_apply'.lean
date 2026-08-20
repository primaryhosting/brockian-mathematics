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

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- Unfolding lemma for `Matrix.toEuclideanLin`. -/

lemma toEuclideanLin_apply' {n : Type*} [Fintype n] [DecidableEq n] {k : Type*}
    (M : Matrix k n 𝕜) (v : EuclideanSpace 𝕜 n) :
    Matrix.toEuclideanLin M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := rfl

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a matrix `Q`, viewed on
`EuclideanSpace 𝕜 m`. -/
