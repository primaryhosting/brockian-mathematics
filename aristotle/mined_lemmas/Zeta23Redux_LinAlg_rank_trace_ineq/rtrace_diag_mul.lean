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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace. -/

lemma rtrace_diag_mul (m : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (Matrix.diagonal (fun i => (m i : ℂ)) * W) = ∑ i, m i * (W i i).re := by
  rw [rtrace_eq_sum_diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diagonal_mul]; simp

