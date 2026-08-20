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

lemma inner_single_left (i : ℕ) (a : ℂ) (g : ℕ →₀ ℂ) :
    ⟪Finsupp.single i a, g⟫_ℂ = (starRingEnd ℂ) a * g i := by
  rw [inner_def, fockInner_eq_sum (Finsupp.single i a) g
    (Finsupp.support_single_subset.trans (by simp)) (Finset.subset_insert i g.support)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg (Ne.symm hj)]
    simp
  · intro hi
    simp at hi

/-- The weight `√n` appearing in the ladder operators. -/
