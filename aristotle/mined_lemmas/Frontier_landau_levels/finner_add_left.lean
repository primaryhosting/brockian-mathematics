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

lemma finner_add_left (f g h : ℕ →₀ ℂ) : finner (f + g) h = finner f h + finner g h := by
  classical
  have h1 : (f + g).support ⊆ f.support ∪ g.support := Finsupp.support_add
  rw [finner_eq_sum _ _ h1, finner_eq_sum f h Finset.subset_union_left,
    finner_eq_sum g h Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [add_mul]

