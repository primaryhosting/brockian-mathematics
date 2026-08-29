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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Basic differential operators on `ℝ³` -/

/-- Physical space `ℝ³`. -/
abbrev Vec3 : Type := Fin 3 → ℝ

/-- The partial derivative `∂f/∂xᵢ` of a scalar field on `ℝ³`. -/

theorem isGlobalSmoothSolution_zero (ν : ℝ) :
    IsGlobalSmoothSolution ν (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  contDiff_u := fun _ => contDiff_const
  contDiff_p := contDiff_const
  initial := fun _ => rfl
  incompressible := fun _ _ _ => by simp [divergence, partialDeriv_zero]
  momentum := fun _ _ _ _ => by
    simp [laplacian, partialDeriv_zero]
  energy := ⟨0, fun _ _ => by simp⟩

/-! ## A nontrivial family of exact solutions -/

/-- The Navier–Stokes system (incompressibility and the momentum equation) for `(u, p)` at all
times, without any decay or energy requirement. -/
