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

theorem fro2_ge (A X : Matrix n n 𝕜) (hA : A.IsHermitian) (hX : X.IsHermitian) :
    2 * RCLike.re (Matrix.trace (X * A)) - fro2 X ≤ fro2 A := by
  have h0 : 0 ≤ fro2 (A - X) := fro2_nonneg _
  have h1 : fro2 (A - X) = fro2 A - 2 * RCLike.re (Matrix.trace (X * A)) + fro2 X := by
    unfold fro2
    rw [Matrix.conjTranspose_sub, hA.eq, hX.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm A X]
    simp only [map_sub]
    ring
  linarith

/-! ### Traces of compressions -/

/-- The trace of `Pr * A * Pr` for Hermitian `Pr`, written as a sum of quadratic forms over
the columns of `Pr`. -/
