import Mathlib

/-!
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of (indices carrying a)
positive eigenvalue. -/

theorem quad_conj (A U D : Matrix n n 𝕜) (hA : A = U * (D * star U)) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x) = star (star U *ᵥ x) ⬝ᵥ (D *ᵥ (star U *ᵥ x)) := by
  subst hA
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp [Matrix.mulVec_mulVec, ← mul_assoc, Matrix.star_eq_conjTranspose]

/-- The real part of the quadratic form of a real diagonal matrix. -/
