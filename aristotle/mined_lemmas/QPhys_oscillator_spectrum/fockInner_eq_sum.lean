import RequestProject.Main

/-!
# A concrete model: the Fock space of finitely supported sequences

This file constructs an explicit `QPhys.LadderSystem`, showing that the hypotheses of
`QPhys.oscillator_spectrum` are consistent (non-vacuous).

The state space is `ℕ →₀ ℂ`, the space of finitely supported complex sequences,
with the usual `ℓ²` inner product `⟪f, g⟫ = ∑ conj (f i) * g i`.  The basis vector
`|n⟩ = single n 1` plays the role of the `n`-th excited state, and the ladder operators
act by `a |n⟩ = √n |n-1⟩`, `a† |n⟩ = √(n+1) |n+1⟩`.
-/

open scoped InnerProductSpace

namespace QPhys

namespace Fock

/-- The `ℓ²` inner product on finitely supported complex sequences. -/

lemma fockInner_eq_sum (f g : ℕ →₀ ℂ) {s : Finset ℕ} (hf : f.support ⊆ s) (hg : g.support ⊆ s) :
    fockInner f g = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  refine Finset.sum_subset (Finset.union_subset hf hg) ?_
  intro i _ hi
  simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, ne_eq, not_not] at hi
  rw [hi.1]
  simp

/-- The inner product space core structure on `ℕ →₀ ℂ`. -/
