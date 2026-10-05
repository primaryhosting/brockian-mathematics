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

lemma froSq_mul_proj_right {F : Matrix n n 𝕜} (hF : F.IsHermitian) (hF2 : F * F = F)
    (M : Matrix n n 𝕜) : froSq (M * F) = rtr (Mᴴ * M * F) := by
  have e1 : (M * F)ᴴ * (M * F) = F * (Mᴴ * M * F) := by
    rw [Matrix.conjTranspose_mul, hF.eq]; simp [Matrix.mul_assoc]
  rw [froSq, e1, rtr_mul_comm, Matrix.mul_assoc (Mᴴ * M) F F, hF2]

