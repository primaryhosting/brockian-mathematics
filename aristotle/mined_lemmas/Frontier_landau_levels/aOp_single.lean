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

lemma aOp_single (m : ℕ) (c : ℂ) :
    aOp (Finsupp.single m c) = Finsupp.single (m - 1) ((Real.sqrt m : ℂ) * c) := by
  ext k
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]

