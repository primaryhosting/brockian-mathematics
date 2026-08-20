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

theorem trace_indicator_proj [DecidableEq n] {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (p : n → Prop)
    [DecidablePred p] :
    RCLike.re (Matrix.trace (U * diagonal (fun i => if p i then (1:𝕜) else 0) * Uᴴ))
      = (Fintype.card {i // p i} : ℝ) := by
  rw [trace_udu hU, Finset.sum_boole, Fintype.card_subtype]
  simp

/-- Trace of a spectral projection against a matrix diagonalised in the same basis. -/
