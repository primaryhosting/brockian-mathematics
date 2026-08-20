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

noncomputable def convective (u : E3 → E3) (x : E3) : E3 := fderiv ℝ u x (u x)

/-! ## The Navier–Stokes system -/

/-- `IsNSSolution ν u p` says that the velocity field `u : ℝ → ℝ³ → ℝ³` and the pressure
`p : ℝ → ℝ³ → ℝ` are smooth in space-time and solve the incompressible Navier–Stokes
equations with viscosity `ν` and zero external force for all times `t ≥ 0`:

* `∇ · u = 0`,
* `∂ₜ u + (u · ∇) u = ν Δ u - ∇ p`.

Smoothness is required on all of `ℝ × ℝ³`, while the equations are only imposed for `t ≥ 0`. -/
structure IsNSSolution (ν : ℝ) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) : Prop where
  smooth_u : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E3 => u q.1 q.2)
  smooth_p : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E3 => p q.1 q.2)
  div_free : ∀ t, 0 ≤ t → ∀ x, divg (u t) x = 0
  momentum : ∀ t, 0 ≤ t → ∀ x,
    deriv (fun s => u s x) t + convective (u t) x = ν • lapl (u t) x - grad (p t) x

/-- Uniform-in-time bound on the kinetic energy of a velocity field, as required in the
statement of the Clay Millennium Problem. -/
