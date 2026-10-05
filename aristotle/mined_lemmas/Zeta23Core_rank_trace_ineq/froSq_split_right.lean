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

lemma froSq_split_right (hE : E.IsHermitian) (hE2 : E * E = E) (M : Matrix n n 𝕜) :
    froSq M = froSq (M * E) + froSq (M * (1 - E)) := by
  rw [froSq_mul_proj_right hE hE2, froSq_mul_proj_right (proj_compl_herm hE) (proj_compl_sq hE2),
    froSq, ← rtr_add, ← Matrix.mul_add]
  simp

/-! ### The quadratic bound -/

/-- If `M` is Hermitian and `E` is a Hermitian projection such that the compression of `M` to the
complement of `E` has nonpositive trace, then `2t·tr M - t²·tr E ≤ ‖M‖_F²` for every `t > 0`.
This is the completion of the square `0 ≤ ‖M - tE‖_F²`. -/
