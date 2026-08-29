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

lemma frobSq_lower {M X : Matrix n n 𝕜} (hM : M.IsHermitian) (hX : X.IsHermitian) :
    2 * rtr (M * X) - rtr (X * X) ≤ frobSq M := by
  have h0 : 0 ≤ frobSq (M - X) := rtr_nonneg (Matrix.posSemidef_conjTranspose_mul_self _)
  have h1 : frobSq (M - X) = rtr ((M - X) * (M - X)) := by
    rw [frobSq, Matrix.conjTranspose_sub, hM, hX]
  have h2 : frobSq M = rtr (M * M) := by rw [frobSq, hM]
  rw [h1, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, rtr_sub, rtr_sub, rtr_sub] at h0
  rw [rtr_mul_comm X M] at h0
  linarith [h2]

/-- The core estimate, stated in terms of abstract projections `Pi` (onto the positive spectral
subspace of `Q`) and `R` (onto the range of `P + Pi`), and the negative part `Qm` of `Q`. -/
