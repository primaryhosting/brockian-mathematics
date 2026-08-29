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

theorem continuous_berryCurvature {A₁ A₂ : ℝ × ℝ → ℝ}
    (h₁ : ContDiff ℝ 1 A₁) (h₂ : ContDiff ℝ 1 A₂) :
    Continuous (berryCurvature A₁ A₂) := by
  have c₁ : Continuous fun x : ℝ × ℝ => fderiv ℝ A₁ x :=
    h₁.continuous_fderiv one_ne_zero
  have c₂ : Continuous fun x : ℝ × ℝ => fderiv ℝ A₂ x :=
    h₂.continuous_fderiv one_ne_zero
  exact (c₂.clm_apply continuous_const).sub (c₁.clm_apply continuous_const)

/-- **Berry phase from Berry curvature.**  For a `C¹` Berry connection `(A₁, A₂)` on a
two-dimensional parameter space, the Berry phase around the closed rectangular loop with
corners `(a₁, a₂)` and `(b₁, b₂)` equals the integral of the Berry curvature
`F = ∂₁A₂ - ∂₂A₁` over the enclosed rectangle (Stokes' theorem in the plane). -/
