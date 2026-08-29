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

@[simp] lemma adagOp_apply (x : ℕ →₀ ℂ) (m : ℕ) :
    adagOp x m = if m = 0 then 0 else (Real.sqrt m : ℂ) * x (m - 1) := rfl

