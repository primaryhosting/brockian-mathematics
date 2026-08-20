import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The Berry curvature `F = ∂_{k₁} A₂ - ∂_{k₂} A₁` of a `U(1)` Berry connection
`(A₁, A₂)` on the Brillouin torus, written in coordinates. -/

noncomputable def berryCurvature (A₁ A₂ : ℝ → ℝ → ℝ) (k₁ k₂ : ℝ) : ℝ :=
  deriv (fun x : ℝ => A₂ x k₂) k₁ - deriv (fun y : ℝ => A₁ k₁ y) k₂

/-- The (first) Chern number of the Berry connection `(A₁, A₂)`: the integral of the
Berry curvature over the Brillouin torus `[0, 2π] × [0, 2π]`, normalized by `2π`. -/
