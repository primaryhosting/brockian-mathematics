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

lemma numberOp_raise {lam : ℂ} {v : V} (hv : numberOp a ad v = lam • v) :
    numberOp a ad (ad v) = (lam + 1) • (ad v) := by
  rw [numberOp_apply] at hv ⊢
  have h2 : a (ad v) = v + ad (a v) := sub_eq_iff_eq_add.mp (hcomm v)
  rw [hv] at h2
  rw [h2, map_add, map_smul, add_smul, one_smul]
  abel

include hadj hcomm in
