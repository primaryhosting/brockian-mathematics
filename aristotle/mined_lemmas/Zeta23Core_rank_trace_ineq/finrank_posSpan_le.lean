/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring; the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix RCLike Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/

lemma finrank_posSpan_le {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    Module.finrank 𝕜 (posSpan hQ) ≤ posIndex hQ := by
  classical
  refine (finrank_span_le_card (R := 𝕜) _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)

/-- On the orthogonal complement of the span of its positive eigenvectors, a Hermitian matrix
has nonpositive quadratic form. -/
