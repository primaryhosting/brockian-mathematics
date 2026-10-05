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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Complexification -/

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`,
as a `ℚ`-linear automorphism. -/

theorem hodgeConjecture_of_span (X : HodgeDatum) (s : Set X.V)
    (hspan : Submodule.span ℚ s = X.hodgeClasses) (hs : ∀ v ∈ s, v ∈ X.alg) :
    HodgeConjecture X := by
  rw [HodgeConjecture, ← hspan, Submodule.span_le]
  exact hs

/-- **Transport along an isomorphism.** The Hodge conjecture only depends on the datum up
to isomorphism: if a `ℚ`-linear isomorphism identifies Hodge classes with Hodge classes and
algebraic classes with algebraic classes, it identifies the two instances of the conjecture. -/
