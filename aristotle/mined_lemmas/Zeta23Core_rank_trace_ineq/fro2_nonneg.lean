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

theorem fro2_nonneg (M : Matrix n n 𝕜) : 0 ≤ fro2 M := by
  unfold fro2
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul]
  simp

/-- The basic quadratic lower bound `‖A‖_F² ≥ 2 Re tr(XA) - ‖X‖_F²`, valid for Hermitian
`A` and `X`; it is just the expansion of `‖A - X‖_F² ≥ 0`. -/
