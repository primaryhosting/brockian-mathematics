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

noncomputable def fockH (hbar omegac : ℝ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  ((hbar * omegac : ℝ) : ℂ) • (adagOp ∘ₗ aOp + (1 / 2 : ℂ) • LinearMap.id)

