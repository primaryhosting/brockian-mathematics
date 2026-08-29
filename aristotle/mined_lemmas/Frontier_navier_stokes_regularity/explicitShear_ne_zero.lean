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

theorem explicitShear_ne_zero (ν : ℝ) : explicitShear ν ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun (congrFun h 0) (fun _ => Real.pi / 2)) 0
  simp [explicitShear] at h1

/-! ## Main statement -/

/-- **Navier–Stokes regularity: formalized statement, base case, and a Lean-checked
reduction.**

The 3D incompressible Navier–Stokes global regularity conjecture itself is recorded as
`Frontier.NavierStokesGlobalRegularity`; it is open and is not proved here.  What is proved
here is:

1. the **base case** of that statement: for every viscosity, the zero initial datum admits a
   global smooth solution with bounded energy;
2. a **Lean-checked reduction**: every smooth solution of the linear heat equation that is
   independent of the first spatial coordinate gives, as a shear flow with vanishing pressure,
   a global smooth solution of the full nonlinear 3D incompressible Navier–Stokes system;
3. an **explicit nonzero** global smooth Navier–Stokes flow obtained from that reduction. -/
