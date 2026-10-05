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

lemma adagOp_single (m : ℕ) (c : ℂ) :
    adagOp (Finsupp.single m c) = Finsupp.single (m + 1) ((Real.sqrt (m + 1) : ℂ) * c) := by
  ext k
  by_cases h0 : k = 0
  · subst h0
    simp
  · by_cases hk : k = m + 1
    · subst hk
      have h1 : (m + 1) - 1 = m := by omega
      simp only [adagOp_apply, h0, if_false, h1, Finsupp.single_eq_same]
      push_cast
      ring
    · have hne : k - 1 ≠ m := by omega
      simp [h0, hk, hne]

/-! ### The canonical commutation relation and the adjoint property -/

