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

def NavierStokesGlobalRegularity : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : Vec → Vec, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, divergence u₀ x = 0) →
    ∃ u p, IsNSSolution nu u p u₀

/-- The same statement, restricted to initial data that are neither identically zero nor a
sinusoidal shear profile `x ↦ sin (k x₂) e₁`; both of those families are solved
unconditionally below (`isNSSolution_zero`, `isNSSolution_shearVelocity`). -/
