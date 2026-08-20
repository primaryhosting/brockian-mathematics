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

lemma rtrace_mul_sq_nonneg {X S : Matrix n n ℂ} (hX : X.PosSemidef) (hS : S.IsHermitian) :
    0 ≤ rtrace (X * (S * S)) := by
  have h2 : Matrix.trace (X * (S * S)) = Matrix.trace (Sᴴ * X * S) := by
    rw [hS.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm (X * S) S, Matrix.mul_assoc]
  have h3 : (Sᴴ * X * S).PosSemidef := hX.conjTranspose_mul_mul_same S
  have h4 := h3.trace_nonneg
  rw [rtrace, h2]
  simpa using (Complex.le_def.mp h4).1

/-! ### Properties of `conjD` -/

omit [Fintype n] in
