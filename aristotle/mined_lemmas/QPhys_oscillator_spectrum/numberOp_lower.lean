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

lemma numberOp_lower {lam : ℂ} {v : V} (hv : numberOp a ad v = lam • v) :
    numberOp a ad (a v) = (lam - 1) • (a v) := by
  rw [numberOp_apply] at hv ⊢
  have hx : a (ad (a v)) = a v + ad (a (a v)) := sub_eq_iff_eq_add.mp (hcomm (a v))
  rw [hv, map_smul] at hx
  rw [sub_smul, one_smul, hx]
  abel

include hcomm in
/-- Raising: `a† v` is an eigenvector with eigenvalue `lam + 1`. -/
