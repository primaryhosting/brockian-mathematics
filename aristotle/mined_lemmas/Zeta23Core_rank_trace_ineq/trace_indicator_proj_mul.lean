import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open Matrix

set_option maxHeartbeats 1000000

namespace Zeta23Core

variable {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- The squared Frobenius norm of a matrix: `‖M‖_F² = Re tr(Mᴴ M)`. -/

theorem trace_indicator_proj_mul [DecidableEq n] {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (p : n → Prop)
    [DecidablePred p] (d : n → ℝ) :
    RCLike.re (Matrix.trace ((U * diagonal (fun i => if p i then (1:𝕜) else 0) * Uᴴ) *
      (U * diagonal (RCLike.ofReal ∘ d) * Uᴴ))) = ∑ i, (if p i then d i else 0) := by
  rw [udu_mul_udu hU, trace_udu hU, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p i <;> simp [h]

/-- On the kernel of the spectral projection attached to `p`, a matrix diagonalised in the
same basis with eigenvalues nonpositive off `p` has nonpositive quadratic form. -/
