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

theorem quad_udu [DecidableEq n] (U : Matrix n n 𝕜) (dd : n → 𝕜) (y : n → 𝕜) :
    star y ⬝ᵥ ((U * diagonal dd * Uᴴ) *ᵥ y)
      = ∑ i, dd i * (star ((Uᴴ *ᵥ y) i) * ((Uᴴ *ᵥ y) i)) := by
  have hs : star y ᵥ* U = star (Uᴴ *ᵥ y) := by simp [Matrix.star_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hs]
  simp [Matrix.mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The trace of the spectral projection attached to a set of indices is its cardinality. -/
