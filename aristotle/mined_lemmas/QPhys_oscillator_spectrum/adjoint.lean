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

lemma adjoint (x y : ℕ →₀ ℂ) : ⟪lower x, y⟫_ℂ = ⟪x, raise y⟫_ℂ := by
  refine Finsupp.induction_linear x ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, inner_add_left, hf, hg]
  · intro m c
    refine Finsupp.induction_linear y ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add, inner_add_right, hf, hg]
    · intro k d
      exact adjoint_single m k c d

/-- The concrete ladder system on the Fock space `ℕ →₀ ℂ`. -/
