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

lemma dotProduct_mulVec_eq_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x)
      = star (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) ⬝ᵥ
        (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ
          (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x)) := by
  rw [star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    ← isHermitian_eq_unitary_mul_diagonal hA]

/-- The real part of a diagonal Hermitian form is a weighted sum of squared norms. -/
