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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ContDiff

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

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

theorem hasGlobalSmoothSolution_zero (ν : ℝ) :
    HasGlobalSmoothSolution ν (fun _ => (0 : Fin 3 → ℝ)) := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, isNSSolution_zero ν, fun _ => rfl, ⟨0, ?_⟩⟩
  intro t _
  simp

/-! ## A Lean-checked reduction: shear flows -/

/-- **Reduction to the linear heat equation.**  If a scalar field `φ` on `ℝ × ℝ³` is smooth,
does not depend on the first spatial coordinate, and solves the heat equation `∂ₜ φ = ν Δφ`,
then the shear flow `u = (φ, 0, 0)` with vanishing pressure is a solution of the full nonlinear
3D incompressible Navier–Stokes system with viscosity `ν`.  In particular the nonlinear
transport term is exactly annihilated by such flows, so for this family global regularity of
Navier–Stokes reduces to global regularity for the linear heat equation. -/
