/-
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues. -/

lemma quadraticForm_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x) = ∑ i, (hA.eigenvalues i : 𝕜) *
      (star ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i *
        ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i) := by
  set U := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hA' : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  conv_lhs => rw [hA']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h2 : star x ᵥ* U = star ((star U) *ᵥ x) := by
    ext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
  rw [h2]
  simp [Matrix.mulVec_diagonal, dotProduct, mul_comm, mul_assoc, mul_left_comm]

/-- The real part of the quadratic form is the weighted sum of squared eigen-coordinates. -/
