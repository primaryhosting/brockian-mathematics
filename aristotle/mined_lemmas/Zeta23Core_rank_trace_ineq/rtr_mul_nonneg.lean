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

lemma rtr_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ rtr (A * B) := by
  have hs := psdSqrt_mul_self hA
  have hh : (psdSqrt hA).IsHermitian := (psdSqrt_posSemidef hA).isHermitian
  have key : (psdSqrt hA * B * (psdSqrt hA)ᴴ).PosSemidef := hB.mul_mul_conjTranspose_same _
  have h3 : (psdSqrt hA * B * (psdSqrt hA)ᴴ).trace = (A * B).trace := by
    rw [hh, Matrix.trace_mul_comm (psdSqrt hA * B) (psdSqrt hA), ← Matrix.mul_assoc, hs]
  have h4 := rtr_nonneg key
  rwa [rtr, h3, ← rtr] at h4

/-- A positive semidefinite matrix with vanishing trace is zero. -/
