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

theorem re_trace_proj_mul_eq (Pr A : Matrix n n 𝕜) (hPr : Prᴴ = Pr) (hPri : Pr * Pr = Pr) :
    RCLike.re (Matrix.trace (Pr * A))
      = ∑ a, RCLike.re (star (fun b => Pr b a) ⬝ᵥ (A *ᵥ (fun b => Pr b a))) := by
  have h : Matrix.trace (Pr * A * Pr) = Matrix.trace (Pr * A) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPri]
  rw [← h, trace_conj_eq_sum Pr A hPr, map_sum]

/-- If `B * C = 0` then `B` annihilates every column of `C`. -/
