/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Basic notions -/

/-- The real part of the trace of a matrix. -/

lemma two_mul_rtr_mul_le {M X : Matrix n n 𝕜} (hM : M.IsHermitian) (hX : X.IsHermitian) :
    2 * rtr (M * X) ≤ froSq M + froSq X := by
  have h0 : 0 ≤ froSq (M - X) := froSq_nonneg _
  have hMX : (M - X)ᴴ = M - X := by rw [Matrix.conjTranspose_sub, hM.eq, hX.eq]
  have hexp : froSq (M - X) = froSq M - 2 * rtr (M * X) + froSq X := by
    rw [froSq, hMX, froSq, froSq, hM.eq, hX.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      rtr_sub, rtr_sub, rtr_sub, rtr_mul_comm X M]
    ring
  linarith

/-! ### Hermitian projections -/

variable {E : Matrix n n 𝕜}

omit [Fintype n] in
