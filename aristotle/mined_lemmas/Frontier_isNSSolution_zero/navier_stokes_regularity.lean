/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped BigOperators

/-- Physical space `ℝ³`. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

theorem navier_stokes_regularity :
    NavierStokesGlobalRegularity ↔ NavierStokesGlobalRegularityReduced := by
  constructor
  · intro h nu hnu u₀ _ _ hsmooth hdiv
    exact h nu hnu u₀ hsmooth hdiv
  · intro h nu hnu u₀ hsmooth hdiv
    by_cases h0 : u₀ = 0
    · subst h0
      exact ⟨fun _ _ => 0, fun _ _ => 0, isNSSolution_zero nu⟩
    by_cases hshear :
        ∃ k : ℝ, u₀ = fun x => Real.sin (k * x 1) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
    · obtain ⟨k, rfl⟩ := hshear
      exact ⟨shearVelocity nu k, fun _ _ => 0, isNSSolution_shearVelocity nu k⟩
    · exact h nu hnu u₀ h0 (by
        intro k hk
        exact hshear ⟨k, hk⟩) hsmooth hdiv

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

