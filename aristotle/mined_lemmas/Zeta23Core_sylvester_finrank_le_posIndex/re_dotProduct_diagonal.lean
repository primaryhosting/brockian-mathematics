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

lemma re_dotProduct_diagonal (d : n → ℝ) (y : n → 𝕜) :
    RCLike.re (star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ d) *ᵥ y)) = ∑ i, d i * ‖y i‖ ^ 2 := by
  rw [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, ← mul_assoc]
  rw [show star (y i) * (RCLike.ofReal (d i) : 𝕜)
      = (RCLike.ofReal (d i) : 𝕜) * star (y i) from mul_comm _ _]
  rw [mul_assoc, RCLike.mul_re]
  simp [RCLike.star_def, RCLike.conj_mul]

/-- The Hermitian form of `A` evaluated at `x` equals `∑ λ i * ‖y i‖ ^ 2`, where `y` are the
coordinates of `x` in the eigenbasis. -/
