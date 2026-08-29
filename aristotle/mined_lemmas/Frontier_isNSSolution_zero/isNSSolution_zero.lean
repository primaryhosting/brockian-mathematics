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

theorem isNSSolution_zero (nu : ℝ) :
    IsNSSolution nu (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) where
  smooth_velocity := contDiff_const
  smooth_pressure := contDiff_const
  initial_condition := fun _ => rfl
  incompressible := fun _ x => divergence_zero x
  momentum := by
    intro t x i
    simp [laplacianComp]

/-! ### A nontrivial exact global solution: the viscously decaying shear flow -/

/-- Partial derivative of a scalar field that depends on a single coordinate. -/
