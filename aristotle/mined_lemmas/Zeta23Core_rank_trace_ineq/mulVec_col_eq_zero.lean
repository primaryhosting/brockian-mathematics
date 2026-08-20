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

theorem mulVec_col_eq_zero {B C : Matrix n n 𝕜} (h : B * C = 0) (a : n) :
    B *ᵥ (fun b => C b a) = 0 := by
  funext c
  have : (B * C) c a = 0 := by rw [h]; simp
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

/-- For Hermitian `B` annihilating `y`, the sesquilinear pairing of `y` with anything in the
range of `B` vanishes. -/
