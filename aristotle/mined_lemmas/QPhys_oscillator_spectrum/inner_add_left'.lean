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

lemma inner_add_left' (f g h : FockSpace) : ⟪f + g, h⟫_ℂ = ⟪f, h⟫_ℂ + ⟪g, h⟫_ℂ := by
  classical
  set s : Finset ℕ := f.support ∪ g.support ∪ h.support with hs
  have hfs : f.support ⊆ s := (Finset.subset_union_left).trans Finset.subset_union_left
  have hgs : g.support ⊆ s := (Finset.subset_union_right).trans Finset.subset_union_left
  have hhs : h.support ⊆ s := Finset.subset_union_right
  have hfg : (f + g).support ⊆ s :=
    (Finsupp.support_add).trans (Finset.union_subset hfs hgs)
  rw [inner_eq_sum hfg hhs, inner_eq_sum hfs hhs, inner_eq_sum hgs hhs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [add_mul]

