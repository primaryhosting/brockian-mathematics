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

lemma rtrace_mul_nonneg {P N : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ rtrace (P * N) := by
  obtain ⟨U, hU, hU', hPd⟩ := hermitian_decomp hP.1
  rw [rtrace_mul_of_decomp hU hU' _ hPd]
  refine Finset.sum_nonneg fun i _ => ?_
  have hWpsd : (Uᴴ * N * U).PosSemidef := by
    have h := hN.mul_mul_conjTranspose_same (Uᴴ)
    simpa using h
  exact mul_nonneg (hP.eigenvalues_nonneg i) (psd_diag_re_nonneg hWpsd i)

/-! ## The rank-trace inequality -/

/-- **Rank-trace inequality** (Lemma 3.2).  Let `P` be positive semidefinite with rank at most `r`,
and let `Q` be Hermitian with at most `b` strictly positive eigenvalues.  Then for every `c > 0`,
`c ⬝ tr P - (c²/4) r + 2c ⬝ tr Q - c² b ≤ ‖P + Q‖_F²`. -/
