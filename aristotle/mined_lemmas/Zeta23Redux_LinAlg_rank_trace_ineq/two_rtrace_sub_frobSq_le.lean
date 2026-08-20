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

lemma two_rtrace_sub_frobSq_le {X T : Matrix n n ℂ} (hX : X.IsHermitian) (hT : T.IsHermitian) :
    2 * rtrace (X * T) - frobSq T ≤ frobSq X := by
  have hnT : (-T).IsHermitian := hT.neg
  have h1 : frobSq (X + (-T)) = frobSq X + 2 * rtrace (X * (-T)) + frobSq (-T) :=
    frobSq_add_of_isHermitian hX hnT
  have h2 : rtrace (X * (-T)) = -rtrace (X * T) := by
    rw [Matrix.mul_neg, rtrace, rtrace, Matrix.trace_neg]
    simp
  have h3 : frobSq (-T) = frobSq T := by
    rw [frobSq, frobSq, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h4 := frobSq_nonneg (X + (-T))
  rw [h1, h2, h3] at h4
  linarith

omit [DecidableEq n] in
/-- If `S` is Hermitian and `X` is positive semidefinite then `Re tr (X * S * S) ≥ 0`. -/
