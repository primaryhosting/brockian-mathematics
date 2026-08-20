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

open MeasureTheory intervalIntegral

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` of a `U(1)` Berry connection `A = (A₁, A₂)`
on the Brillouin zone. -/

theorem berryCurvature_eq
    (hdx : ∀ x y : ℝ, HasDerivAt (fun t => A₂ t y) (D₂ x y) x)
    (hdy : ∀ x y : ℝ, HasDerivAt (fun t => A₁ x t) (D₁ x y) y) (x y : ℝ) :
    berryCurvature A₁ A₂ x y = D₂ x y - D₁ x y := by
  simp [berryCurvature, (hdx x y).deriv, (hdy x y).deriv]

/-- Fubini's theorem for a continuous function on the square `[0, L] × [0, L]`. -/
