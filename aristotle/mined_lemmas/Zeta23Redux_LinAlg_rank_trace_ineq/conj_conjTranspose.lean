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

lemma conj_conjTranspose {U : Matrix (Fin d) (Fin d) ℂ} (M : Matrix (Fin d) (Fin d) ℂ) :
    (U * M * Uᴴ)ᴴ = U * Mᴴ * Uᴴ := by
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

