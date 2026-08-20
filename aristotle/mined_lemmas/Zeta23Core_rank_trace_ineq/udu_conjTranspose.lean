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

theorem udu_conjTranspose [DecidableEq n] (U : Matrix n n 𝕜) {d : n → 𝕜} (hd : ∀ i, star (d i) = d i) :
    (U * diagonal d * Uᴴ)ᴴ = U * diagonal d * Uᴴ := by
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.diagonal_conjTranspose,
    show (star d) = d from funext hd]

