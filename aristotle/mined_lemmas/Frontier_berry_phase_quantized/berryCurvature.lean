/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

open MeasureTheory Set intervalIntegral
open scoped Interval

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` of a Berry connection with components
`A₁, A₂ : ℝ × ℝ → ℝ` on a two-dimensional parameter space. -/

noncomputable def berryCurvature (A₁ A₂ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fderiv ℝ A₂ x (1, 0) - fderiv ℝ A₁ x (0, 1)

/-- The Berry phase accumulated along the closed rectangular loop with corners
`(a₁, a₂)`, `(b₁, a₂)`, `(b₁, b₂)`, `(a₁, b₂)`, traversed counterclockwise:
`∮ A · dl`. -/
