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

noncomputable def berryCurvature (A₁ A₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1)

/-- The Berry phase accumulated along the (counterclockwise) closed rectangular loop with
corners `(a₁, a₂)`, `(b₁, a₂)`, `(b₁, b₂)`, `(a₁, b₂)`, i.e. the line integral
`∮ A₁ dx + A₂ dy` of the Berry connection along that loop. -/
