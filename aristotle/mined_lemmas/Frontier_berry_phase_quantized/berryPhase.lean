/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
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

/-- The Berry curvature of a Berry connection one-form `A = A₁ dx + A₂ dy` on the
(two–dimensional) parameter space `ℝ × ℝ`: it is the exterior derivative
`F = ∂₁A₂ - ∂₂A₁`. -/

noncomputable def berryPhase (A₁ A₂ : ℝ × ℝ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  (∫ x in a₁..b₁, A₁ (x, a₂)) + (∫ y in a₂..b₂, A₂ (b₁, y))
    - (∫ x in a₁..b₁, A₁ (x, b₂)) - (∫ y in a₂..b₂, A₂ (a₁, y))

/-- **Berry phase = flux of the Berry curvature.**

For a continuously differentiable Berry connection `A = A₁ dx + A₂ dy` on the parameter plane,
the Berry phase around the closed rectangular loop with corners `(a₁, a₂)` and `(b₁, b₂)` equals
the integral of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` over the enclosed rectangle.

This is Stokes'/Green's theorem in the plane; it is deduced from Mathlib's divergence theorem
`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`. -/
