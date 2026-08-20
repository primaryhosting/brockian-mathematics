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

lemma inner_smul_left' (f g : FockSpace) (r : ℂ) :
    ⟪r • f, g⟫_ℂ = (starRingEnd ℂ) r * ⟪f, g⟫_ℂ := by
  classical
  set s : Finset ℕ := f.support ∪ g.support with hs
  have hfs : f.support ⊆ s := Finset.subset_union_left
  have hgs : g.support ⊆ s := Finset.subset_union_right
  have hrf : (r • f).support ⊆ s := (Finsupp.support_smul).trans hfs
  rw [inner_eq_sum hrf hgs, inner_eq_sum hfs hgs, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_assoc]

noncomputable instance : NormedAddCommGroup FockSpace :=
  letI : InnerProductSpace.Core ℂ FockSpace :=
    { conj_inner_symm := inner_conj_symm'
      re_inner_nonneg := inner_self_re_nonneg
      add_left := inner_add_left'
      smul_left := inner_smul_left'
      definite := inner_definite }
  this.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℂ FockSpace := .ofCore _

