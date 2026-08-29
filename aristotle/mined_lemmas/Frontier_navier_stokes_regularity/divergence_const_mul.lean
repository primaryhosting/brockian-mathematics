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

theorem divergence_const_mul {u : Vec3 → Vec3} (hu : ∀ i, Differentiable ℝ (fun y => u y i))
    (c : ℝ) (x : Vec3) :
    divergence (fun y j => c * u y j) x = c * divergence u x := by
  unfold divergence
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => partialDeriv_const_mul (hu i) c i x

/-- The Navier–Stokes scaling symmetry: global regularity for one positive viscosity implies
global regularity for every positive viscosity.  The proof rescales a solution `u` for viscosity
`ν` into `v (t, x) = a • u (a t, x)`, with pressure `a² p (a t, x)` and `a = μ / ν`, which solves
the equations for viscosity `μ` with initial datum `a • u₀`. -/
