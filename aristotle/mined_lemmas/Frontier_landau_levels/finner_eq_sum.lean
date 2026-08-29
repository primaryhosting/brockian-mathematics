/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

lemma finner_eq_sum (f g : ℕ →₀ ℂ) {s : Finset ℕ} (hs : f.support ⊆ s) :
    finner f g = ∑ i ∈ s, (starRingEnd ℂ) (f i) * g i := by
  refine Finset.sum_subset hs ?_
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi]
  simp

