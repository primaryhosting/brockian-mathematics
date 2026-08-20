/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux
namespace LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a complex matrix. -/

lemma rtrace_conjD (U : Matrix.unitaryGroup n ℂ) (f : n → ℝ) :
    rtrace (conjD U f) = ∑ i, f i := by
  have h : (star (U : Matrix n n ℂ)) * (U : Matrix n n ℂ) = 1 := U.2.1
  rw [rtrace, conjD, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp

