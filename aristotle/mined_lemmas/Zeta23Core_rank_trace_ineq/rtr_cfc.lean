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

lemma rtr_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rtr (hA.cfc f) = ∑ i, f (hA.eigenvalues i) := by
  rw [rtr, cfc_eq_conj, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    eigenvectorUnitary_conjTranspose_mul, Matrix.one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

