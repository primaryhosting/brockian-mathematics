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

def HasGlobalSmoothSolution (ν : ℝ) (u₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∃ (u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)) (P : ℝ → (Fin 3 → ℝ) → ℝ),
    IsNSSolution ν u P ∧ (∀ x, u 0 x = u₀ x) ∧ BoundedEnergy u

/-- **Global regularity for the 3D incompressible Navier–Stokes equations** (the statement of
the Clay Millennium Problem: existence and smoothness on `ℝ³`).

For every positive viscosity `ν` and every divergence-free Schwartz initial velocity field `u₀`
on `ℝ³`, the Navier–Stokes system with no external force admits a globally defined smooth
solution `(u, P)` with `u(0, ·) = u₀` and with uniformly bounded energy.

This proposition is *not* proved here: it records the statement of the open problem.
(Smoothness of the solution is formalized as smoothness on all of `ℝ × ℝ³`, the equations being
required for `t ≥ 0`.) -/
