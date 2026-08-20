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

lemma inner_eigenvectorBasis_apply {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (i : m)
    (x : EuclideanSpace 𝕜 m) :
    inner 𝕜 (hQ.eigenvectorBasis i) (Matrix.toEuclideanLin Q x)
      = (hQ.eigenvalues i : 𝕜) * inner 𝕜 (hQ.eigenvectorBasis i) x := by
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin Q) = Matrix.toEuclideanLin Q := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hQ.eq]
  rw [← LinearMap.adjoint_inner_left, hadj, toEuclideanLin_eigenvectorBasis hQ i, inner_smul_left]
  simp

/-- Diagonalisation of the quadratic form in the eigenbasis. -/
