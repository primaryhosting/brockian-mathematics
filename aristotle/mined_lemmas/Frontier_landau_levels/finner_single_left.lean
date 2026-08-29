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

lemma finner_single_left (m : ℕ) (c : ℂ) (g : ℕ →₀ ℂ) :
    finner (Finsupp.single m c) g = (starRingEnd ℂ) c * g m := by
  rw [finner_eq_sum _ _ (Finsupp.support_single_subset (a := m) (b := c))]
  simp

