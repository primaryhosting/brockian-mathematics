/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma conj_mul {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1)
    (M N : Matrix (Fin d) (Fin d) ℂ) :
    (U * M * Uᴴ) * (U * N * Uᴴ) = U * (M * N) * Uᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U (N * Uᴴ), hU, Matrix.one_mul]

