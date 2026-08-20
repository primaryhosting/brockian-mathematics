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

lemma inner_single_single (m n : ℕ) (u v : ℂ) :
    ⟪(Finsupp.single m u : FockSpace), (Finsupp.single n v : FockSpace)⟫_ℂ
      = if m = n then (starRingEnd ℂ) u * v else 0 := by
  classical
  have hm : (Finsupp.single m u : FockSpace).support ⊆ ({m, n} : Finset ℕ) :=
    (Finsupp.support_single_subset).trans (by simp)
  have hn : (Finsupp.single n v : FockSpace).support ⊆ ({m, n} : Finset ℕ) :=
    (Finsupp.support_single_subset).trans (by simp)
  rw [inner_eq_sum hm hn]
  by_cases h : m = n
  · subst h
    simp
  · rw [Finset.sum_pair h]
    simp [h, Ne.symm h]

/-- The annihilation (lowering) operator, `a eₙ = √n eₙ₋₁`. -/
