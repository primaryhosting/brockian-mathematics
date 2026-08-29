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

lemma conj_herm {S : Matrix n n 𝕜} (hE : E.IsHermitian) (hS : S.IsHermitian) :
    (E * S * E).IsHermitian := by
  show (E * S * E)ᴴ = E * S * E
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hE.eq, hS.eq, Matrix.mul_assoc]

omit [DecidableEq n] in
