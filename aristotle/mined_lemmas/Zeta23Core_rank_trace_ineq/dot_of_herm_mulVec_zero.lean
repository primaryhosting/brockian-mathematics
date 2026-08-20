import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open Matrix

set_option maxHeartbeats 1000000

namespace Zeta23Core

variable {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- The squared Frobenius norm of a matrix: `‖M‖_F² = Re tr(Mᴴ M)`. -/

theorem dot_of_herm_mulVec_zero {B : Matrix n n 𝕜} (hB : Bᴴ = B) {y : n → 𝕜} (w : n → 𝕜)
    (hy : B *ᵥ y = 0) : star y ⬝ᵥ (B *ᵥ w) = 0 := by
  have hs : star y ᵥ* B = star (Bᴴ *ᵥ y) := by simp [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec, hs, hB, hy]
  simp

/-! ### Spectral projections -/

