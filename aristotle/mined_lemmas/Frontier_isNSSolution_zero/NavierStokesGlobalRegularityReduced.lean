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

def NavierStokesGlobalRegularityReduced : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : Vec → Vec, u₀ ≠ 0 →
    (∀ k : ℝ, u₀ ≠ fun x => Real.sin (k * x 1) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) →
    ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, divergence u₀ x = 0) → ∃ u p, IsNSSolution nu u p u₀

