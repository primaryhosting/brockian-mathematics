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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index (number of positive eigenvalues) of a Hermitian matrix. -/

lemma isHermitian_eq_unitary_mul_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply]

/-- The Hermitian form of `A` in the eigenbasis coordinates. -/
