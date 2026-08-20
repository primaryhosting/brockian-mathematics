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

lemma rtrace_mul_conjD_nonneg {X : Matrix n n ℂ} (hX : X.PosSemidef)
    (U : Matrix.unitaryGroup n ℂ) {f : n → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ rtrace (X * conjD U f) := by
  have hsplit : conjD U f = conjD U (fun i => Real.sqrt (f i)) * conjD U (fun i => Real.sqrt (f i)) := by
    rw [conjD_mul]
    congr 1
    funext i
    exact (Real.mul_self_sqrt (hf i)).symm
  rw [hsplit]
  exact rtrace_mul_sq_nonneg hX (conjD_isHermitian U _)

/-! ### The two halves of the argument -/

/-- With `Π` the spectral projection onto the range of `P` (scaled by `c/2`) as test matrix,
`frobSq (P - R) ≥ c * rtrace P - c * rtrace R - (c²/4) * rank P` for positive semidefinite
`P` and `R`. -/
