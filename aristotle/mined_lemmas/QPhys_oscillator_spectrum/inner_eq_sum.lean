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

lemma inner_eq_sum {f g : FockSpace} {s : Finset ℕ} (hf : f.support ⊆ s) (hg : g.support ⊆ s) :
    ⟪f, g⟫_ℂ = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  rw [inner_def]
  refine Finset.sum_subset (Finset.union_subset hf hg) ?_
  intro i _ hi
  simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hi
  rw [hi.1]
  simp

