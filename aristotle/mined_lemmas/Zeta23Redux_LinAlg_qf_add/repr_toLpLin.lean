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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

open Matrix Finset Module

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, M x⟫` associated with a matrix `M`, on `EuclideanSpace ℂ (Fin d)`.
-/

lemma repr_toLpLin (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
    hM.eigenvectorBasis.repr (Matrix.toLpLin 2 2 M x) j
      = (hM.eigenvalues j : ℂ) * hM.eigenvectorBasis.repr x j := by
  have hsym := Matrix.isHermitian_iff_isSymmetric.1 hM
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have h1 : (inner ℂ (hM.eigenvectorBasis j) (Matrix.toLpLin 2 2 M x) : ℂ)
      = inner ℂ (Matrix.toLpLin 2 2 M (hM.eigenvectorBasis j)) x := (hsym _ _).symm
  rw [h1, toLpLin_eigenvectorBasis hM j, inner_smul_left]
  simp

/-- Diagonalization of the quadratic form of a Hermitian matrix in its eigenbasis. -/
