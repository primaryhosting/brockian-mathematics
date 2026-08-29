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

noncomputable def adagFun (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (x.support.image (fun i => i + 1))
    (fun m => if m = 0 then 0 else (Real.sqrt m : ℂ) * x (m - 1))
    (by
      intro m hm
      by_cases h0 : m = 0
      · simp [h0] at hm
      · have hx : x (m - 1) ≠ 0 := fun h => hm (by simp [h0, h])
        refine Finset.mem_image.mpr ⟨m - 1, Finsupp.mem_support_iff.mpr hx, ?_⟩
        omega)

