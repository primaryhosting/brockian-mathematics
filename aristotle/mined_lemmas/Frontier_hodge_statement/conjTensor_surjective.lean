/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation, viewed as a `ℚ`-linear endomorphism of `ℂ`. -/

lemma conjTensor_surjective (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Surjective (conjTensor V) := by
  intro x
  refine ⟨conjTensor V x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z v => simp [conjTensor, conjQ]
  | add a b ha hb => simp [map_add, ha, hb]

/-! ## Rational Hodge structures -/

/-- A pure rational Hodge structure of weight `w` on a finite-dimensional `ℚ`-vector space `V`:
a decomposition of the complexification `V ⊗ ℂ = ⨁_{p+q = w} V^{p,q}` into complex subspaces
(indexed here by `p`, with `q = w - p`), which is exchanged by complex conjugation:
`conj (V^{p,q}) = V^{q,p}`. -/
structure HodgeStructure (w : ℤ) (V : Type) [AddCommGroup V] [Module ℚ V] where
  /-- The `(p, w - p)` piece of the Hodge decomposition of the complexification. -/
  piece : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The pieces give an internal direct sum decomposition of `ℂ ⊗[ℚ] V`. -/
  internal : DirectSum.IsInternal piece
  /-- Complex conjugation carries the `(p, w - p)` piece onto the `(w - p, p)` piece. -/
  conj_piece : ∀ p : ℤ,
    ((piece p).restrictScalars ℚ).map (conjTensor V) = (piece (w - p)).restrictScalars ℚ

/-- The space of *Hodge classes* of a weight-`2p` rational Hodge structure `H`:
the rational classes `v ∈ V` whose image `1 ⊗ v` in the complexification lies in the
`(p, p)`-piece.  This is a `ℚ`-subspace of `V`. -/
