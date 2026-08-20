import RequestProject.Main

/-!
# A concrete model for the ladder-operator hypotheses

This file exhibits a concrete inner product space carrying ladder operators satisfying the
hypotheses of `QPhys.oscillator_spectrum`, so that the theorem is not vacuous.

The model is the algebraic Fock space of finitely supported complex sequences `ℕ →₀ ℂ`, with
`a (eₙ) = √n eₙ₋₁` and `a† (eₙ) = √(n+1) eₙ₊₁`.
-/

open scoped InnerProductSpace
open Finsupp

namespace QPhys

/-- The algebraic Fock space: finitely supported complex sequences. -/
abbrev FockSpace : Type := ℕ →₀ ℂ

namespace FockSpace

/-- The inner product on the algebraic Fock space. -/

lemma numberOp_apply (x : V) : numberOp a ad x = ad (a x) := rfl

variable (hadj : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
  (hcomm : ∀ x : V, a (ad x) - ad (a x) = x)

include hadj in
/-- For an eigenvector of the number operator, the eigenvalue times `‖v‖²` equals `‖a v‖²`. -/
