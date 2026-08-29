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

lemma rtrace_mul_of_decomp {U P N : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (m : Fin d → ℝ) (hP : P = U * Matrix.diagonal (fun i => (m i : ℂ)) * Uᴴ) :
    rtrace (P * N) = ∑ i, m i * ((Uᴴ * N * U) i i).re := by
  have h : P * N = U * (Matrix.diagonal (fun i => (m i : ℂ)) * (Uᴴ * N * U)) * Uᴴ := by
    rw [hP]; simp only [Matrix.mul_assoc, hU', Matrix.mul_one]
  rw [h, rtrace_conj hU, rtrace_diag_mul]

