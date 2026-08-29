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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index (number of positive eigenvalues) of a Hermitian matrix. -/

theorem re_quadratic_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set y : n → 𝕜 := star U *ᵥ x with hy
  have hAx : A *ᵥ x = U *ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, hy, hU]
    rw [mulVec_mulVec, mulVec_mulVec]
  have hstar : star x ᵥ* U = star y := by
    rw [hy, star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have key : star x ⬝ᵥ (A *ᵥ x)
      = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    rw [hAx, dotProduct_mulVec, hstar]
  rw [key]
  rw [dotProduct]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [mulVec_diagonal]
  have : star y i * ((RCLike.ofReal ∘ hA.eigenvalues) i * y i)
      = (hA.eigenvalues i : 𝕜) * ((‖y i‖ ^ 2 : ℝ) : 𝕜) := by
    simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def]
    rw [show ((‖y i‖ ^ 2 : ℝ) : 𝕜) = ((‖y i‖ : 𝕜)) ^ 2 by push_cast; ring, ← RCLike.conj_mul]
    ring
  rw [this]
  simp

/-- **Sylvester's law of inertia, hard direction.** If a Hermitian matrix `A` is positive
definite on a subspace `W` of `n → 𝕜` (i.e. `Re (xᴴ A x) > 0` for every nonzero `x ∈ W`),
then `dim W ≤ n₊(A)`, the number of positive eigenvalues of `A`. -/
