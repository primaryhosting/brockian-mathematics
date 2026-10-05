import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
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

open Matrix

namespace Zeta23Redux.LinAlg

/-- The eigencoordinates of a vector `x` with respect to the (unitary) eigenvector basis of a
Hermitian matrix `A`: the components of `x` in the orthonormal eigenbasis, i.e. `Uᴴ *ᵥ x` where
`U` is the unitary matrix of eigenvectors from the spectral theorem. -/

private theorem quad_conj {n : Type*} [Fintype n] [DecidableEq n] (U D : Matrix n n ℂ)
    (x : n → ℂ) :
    star x ⬝ᵥ (U * D * Uᴴ) *ᵥ x = star (Uᴴ *ᵥ x) ⬝ᵥ (D *ᵥ (Uᴴ *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- The quadratic form of a real diagonal matrix is the weighted sum of squared norms. -/
