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

noncomputable def aFun (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (x.support.image (fun i => i - 1))
    (fun m => (Real.sqrt (m + 1) : ℂ) * x (m + 1))
    (by
      intro m hm
      have hx : x (m + 1) ≠ 0 := fun h => hm (by simp [h])
      exact Finset.mem_image.mpr ⟨m + 1, Finsupp.mem_support_iff.mpr hx, by simp⟩)

