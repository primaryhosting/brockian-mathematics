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

lemma adjoint_rel (x y : FockSpace) : ⟪annihilate x, y⟫_ℂ = ⟪x, create y⟫_ℂ := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, inner_add_left, hf, hg]
  | single m u =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [map_add, inner_add_right, hf, hg]
    | single n v => exact adjoint_single m n u v

/-- The canonical commutation relation `[a, a†] = 1`. -/
