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
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a matrix. -/

lemma posSemidef_mul_eq_zero {T K : Matrix n n 𝕜} (hT : T.PosSemidef)
    (h : Kᴴ * T * K = 0) : T * K = 0 := by
  have hh : (psdSqrt hT).IsHermitian := (psdSqrt_posSemidef hT).isHermitian
  have hzero : (psdSqrt hT * K)ᴴ * (psdSqrt hT * K) = 0 := by
    rw [Matrix.conjTranspose_mul, hh, Matrix.mul_assoc, ← Matrix.mul_assoc (psdSqrt hT),
      psdSqrt_mul_self, ← Matrix.mul_assoc, h]
  have h0 : psdSqrt hT * K = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  rw [← psdSqrt_mul_self hT, Matrix.mul_assoc, h0, Matrix.mul_zero]

/-! ### Generic linear algebra helpers -/

omit [DecidableEq n] in
