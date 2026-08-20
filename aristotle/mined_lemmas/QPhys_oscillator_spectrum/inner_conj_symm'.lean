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

lemma inner_conj_symm' (f g : FockSpace) :
    (starRingEnd ℂ) (⟪g, f⟫_ℂ) = ⟪f, g⟫_ℂ := by
  rw [inner_eq_sum (s := f.support ∪ g.support) Finset.subset_union_right
      Finset.subset_union_left,
    inner_eq_sum (s := f.support ∪ g.support) Finset.subset_union_left Finset.subset_union_right,
    map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_comm]

