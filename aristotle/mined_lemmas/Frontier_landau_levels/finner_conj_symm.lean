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

lemma finner_conj_symm (f g : ℕ →₀ ℂ) :
    (starRingEnd ℂ) (finner g f) = finner f g := by
  classical
  rw [finner_eq_sum g f Finset.subset_union_right (s := f.support ∪ g.support),
    finner_eq_sum f g Finset.subset_union_left (s := f.support ∪ g.support), map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_comm]

