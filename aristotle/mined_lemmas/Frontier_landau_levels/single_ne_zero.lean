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

theorem single_ne_zero (n : ℕ) : Finsupp.single n (1 : ℂ) ≠ 0 := by
  simp

/-- The Landau Hamiltonian `H = ℏ ω_c (a† a + 1/2)` on the Fock model. -/
