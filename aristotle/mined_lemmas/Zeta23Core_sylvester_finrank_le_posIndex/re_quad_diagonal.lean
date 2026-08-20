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

theorem re_quad_diagonal (d : n → ℝ) (y : n → 𝕜) :
    RCLike.re (star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ d) *ᵥ y)) = ∑ i, d i * ‖y i‖ ^ 2 := by
  rw [dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  simp [RCLike.star_def, mul_comm, ← RCLike.normSq_eq_def', RCLike.normSq_apply]
  ring

/-- Diagonalization of a Hermitian matrix, in the form `A = U * (D * Uᴴ)`. -/
