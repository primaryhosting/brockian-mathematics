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

lemma froSq_split_left (hE : E.IsHermitian) (hE2 : E * E = E) (M : Matrix n n 𝕜) :
    froSq M = froSq (E * M) + froSq ((1 - E) * M) := by
  have hc := proj_compl_herm hE
  have h1 : froSq (E * M) = rtr (Mᴴ * E * M) := by
    rw [froSq, Matrix.conjTranspose_mul, hE.eq, ← Matrix.mul_assoc, Matrix.mul_assoc Mᴴ E E, hE2]
  have h2 : froSq ((1 - E) * M) = rtr (Mᴴ * (1 - E) * M) := by
    rw [froSq, Matrix.conjTranspose_mul, hc.eq, ← Matrix.mul_assoc,
      Matrix.mul_assoc Mᴴ (1 - E) (1 - E), proj_compl_sq hE2]
  rw [h1, h2, froSq, ← rtr_add, ← Matrix.add_mul, ← Matrix.mul_add]
  simp

