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

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

def SolvableData (ν : ℝ) (u₀ : E3 → E3) : Prop :=
  ∃ u : ℝ → E3 → E3, ∃ p : ℝ → E3 → ℝ,
    IsNSSolution ν u p ∧ (∀ x, u 0 x = u₀ x) ∧ BoundedEnergy u

/-- **Global regularity for the three dimensional incompressible Navier–Stokes equations**
(the Clay Millennium Problem, case of zero external force): for every viscosity `ν > 0` and
every divergence free Schwartz initial datum `u₀` on `ℝ³` there exist a smooth velocity field
and pressure, defined for all times, solving the Navier–Stokes system with datum `u₀` and with
uniformly bounded kinetic energy. -/
