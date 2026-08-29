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

lemma isHermitian_rsmul {X : Matrix (Fin d) (Fin d) ℂ} (t : ℝ) (hX : X.IsHermitian) :
    (((t : ℂ)) • X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hX.eq]
  simp

/-- The real part of the trace of a positive semidefinite matrix is nonnegative. -/
