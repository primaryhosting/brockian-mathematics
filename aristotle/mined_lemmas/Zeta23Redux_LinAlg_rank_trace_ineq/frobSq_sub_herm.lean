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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Unitary

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace of a matrix. -/

lemma frobSq_sub_herm {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobSq (X - Y) = frobSq X + frobSq Y - 2 * rtrace (X * Y) := by
  simp only [frobSq, Matrix.conjTranspose_sub, hX.eq, hY.eq, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, Complex.sub_re, rtrace]
  rw [Matrix.trace_mul_comm Y X]
  ring

/-- The basic scalar inequality `‖X‖_F² ≥ 2 Re tr (X M) - ‖M‖_F²`, coming from
`‖X - M‖_F² ≥ 0`.  This is the matrix form of `x² ≥ 2 m x - m²`. -/
