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

lemma frobSq_add_of_isHermitian {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobSq (X + Y) = frobSq X + 2 * rtrace (X * Y) + frobSq Y := by
  have h1 : (X + Y)ᴴ * (X + Y) = X * X + X * Y + (Y * X + Y * Y) := by
    rw [Matrix.conjTranspose_add, hX.eq, hY.eq]
    noncomm_ring
  rw [frobSq, h1]
  simp only [Matrix.trace_add, Complex.add_re]
  have h2 : (Matrix.trace (Y * X)).re = (Matrix.trace (X * Y)).re := by
    rw [Matrix.trace_mul_comm]
  rw [frobSq, frobSq, hX.eq, hY.eq, rtrace, h2]
  ring

omit [DecidableEq n] in
/-- The basic "test matrix" bound: `‖X‖² ≥ 2⟨X,T⟩ - ‖T‖²`. -/
