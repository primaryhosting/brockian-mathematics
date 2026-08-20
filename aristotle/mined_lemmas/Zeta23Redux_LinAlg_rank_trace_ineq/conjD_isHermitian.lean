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

lemma conjD_isHermitian (U : Matrix.unitaryGroup n ℂ) (f : n → ℝ) :
    (conjD U f).IsHermitian := by
  unfold Matrix.IsHermitian conjD
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, diagonal_ofReal_conjTranspose]
  simp [Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose]

