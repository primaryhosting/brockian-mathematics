import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a matrix. -/

lemma cfc_rank_le (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).rank ≤ Fintype.card {i // f (hA.eigenvalues i) ≠ 0} := by
  rw [cfc_eq_conj]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  refine le_trans (Matrix.rank_mul_le_right _ _) ?_
  rw [Matrix.rank_diagonal]
  exact le_of_eq (Fintype.card_congr (Equiv.subtypeEquivRight (by
    intro _
    simp [Function.comp_def])))

end CFC

/-! ### Square roots and positivity of traces -/

/-- The positive semidefinite square root, built from the functional calculus. -/
