/-
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
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

open Matrix Unitary

/-- The number of positive eigenvalues of a Hermitian matrix `A`, i.e. `n₊(A)`. -/

theorem re_quadraticForm_eq_sum_of_spectral_decomposition {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] [DecidableEq n] (A U : Matrix n n 𝕜) (d : n → ℝ)
    (hspec : A = U * diagonal (RCLike.ofReal ∘ d) * star U) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) = ∑ i, d i * ‖(star U *ᵥ x) i‖ ^ 2 := by
  have h1 : star x ⬝ᵥ (A *ᵥ x)
      = star (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ d) *ᵥ (star U *ᵥ x)) := by
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      ← Matrix.star_eq_conjTranspose, star_star]
  rw [h1, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, ← mul_assoc, RCLike.star_def]
  rw [mul_comm (starRingEnd 𝕜 _), mul_assoc, RCLike.conj_mul]
  simp

/-- **Sylvester's law of inertia**, hard direction: if the Hermitian form associated with a
Hermitian matrix `A` is positive definite on a subspace `W` of `n → 𝕜`, then
`finrank 𝕜 W ≤ posIndex hA`, the number of positive eigenvalues of `A`. -/
