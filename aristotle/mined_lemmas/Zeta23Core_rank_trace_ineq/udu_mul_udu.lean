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

theorem udu_mul_udu [DecidableEq n] {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (d e : n → 𝕜) :
    (U * diagonal d * Uᴴ) * (U * diagonal e * Uᴴ) = U * diagonal (fun i => d i * e i) * Uᴴ := by
  rw [← Matrix.diagonal_mul_diagonal]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

