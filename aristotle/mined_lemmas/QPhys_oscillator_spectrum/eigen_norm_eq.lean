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

lemma eigen_norm_eq {lam : ℂ} {v : V} (hv : numberOp a ad v = lam • v) :
    lam * ((‖v‖ : ℂ) ^ 2) = ((‖a v‖ : ℂ) ^ 2) := by
  have h1 : ⟪v, ad (a v)⟫_ℂ = ⟪a v, a v⟫_ℂ := (hadj v (a v)).symm
  have e1 : ⟪v, v⟫_ℂ = ((‖v‖ : ℂ)) ^ 2 := by
    simp
  have e2 : ⟪a v, a v⟫_ℂ = ((‖a v‖ : ℂ)) ^ 2 := by
    simp
  rw [numberOp_apply] at hv
  rw [hv, inner_smul_right, e1, e2] at h1
  exact h1

include hadj in
/-- Eigenvalues of the number operator are nonnegative reals. -/
