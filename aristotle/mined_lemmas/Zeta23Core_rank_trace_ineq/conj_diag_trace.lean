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

lemma conj_diag_trace {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (d : n → 𝕜) :
    (U * diagonal d * Uᴴ).trace = ∑ i, d i := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one,
    Matrix.trace_diagonal]

/-- Every Hermitian matrix `M` admits a Hermitian projection `E` onto the span of the
eigenvectors with positive eigenvalue: its trace is the positive index of inertia of `M`,
and the compression of `M` to the orthogonal complement is negative semidefinite. -/
