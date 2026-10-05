/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open scoped Pointwise
open scoped ComplexOrder

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Basic notions -/

/-- The real part of the trace of a matrix. -/

lemma posIndex_eq_rank {W : Matrix n n 𝕜} (hW : W.PosSemidef) :
    posIndex hW.isHermitian = W.rank := by
  classical
  rw [hW.isHermitian.rank_eq_card_non_zero_eigs, posIndex, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  have h := hW.eigenvalues_nonneg i
  constructor
  · intro hi; exact ne_of_gt hi
  · intro hi; exact lt_of_le_of_ne h (Ne.symm hi)

/-! ### The rank–trace inequality -/

/-- **Rank–trace inequality** (Lemma 3.2 of the preprint).

Let `P` be positive semidefinite of rank at most `r`, let `Q` be Hermitian with at most `b`
positive eigenvalues, and let `c > 0`. Then
`c·Re tr P - (c²/4)·r + 2c·Re tr Q - c²·b ≤ ‖P + Q‖_F²`,
where `‖M‖_F² = Re tr (Mᴴ M)`. -/
