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

theorem satisfiesNSEquations_uniform (ν : ℝ) (f : ℝ → Vec3) :
    SatisfiesNSEquations ν (fun t _ => f t)
      (fun t x => -∑ k, deriv (fun s => f s k) t * x k) := by
  constructor
  · intro t x
    simp [divergence, partialDeriv_const]
  · intro t x j
    rw [partialDeriv_linear (fun k => deriv (fun s => f s k) t) j x]
    simp [laplacian, partialDeriv_const]

/-! ## Main statement -/

/-- **Navier–Stokes regularity (formalized statement, base case and Lean-checked reduction).**

The first component is the Lean-checked reduction: global smoothness/existence for the
3D incompressible Navier–Stokes equations at *any* positive viscosity is equivalent to global
smoothness/existence at viscosity `1`; i.e. the Millennium problem for all viscosities reduces to
the single normalized case `ν = 1` (equivalently, in contrapositive form, a finite-energy blow-up
for some viscosity produces one for viscosity `1`).

The second component is the base case: for every viscosity the trivial initial datum admits a
global smooth finite-energy solution. -/
