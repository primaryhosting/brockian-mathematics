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

noncomputable def fockInnerStruct : Inner ℂ (ℕ →₀ ℂ) := ⟨finner⟩

attribute [local instance] fockInnerStruct

/-- The inner product space core on finitely supported complex sequences. -/
