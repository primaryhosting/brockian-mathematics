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

lemma finner_self_nonneg (f : ℕ →₀ ℂ) : 0 ≤ (finner f f).re := by
  rw [finner_self_eq]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

