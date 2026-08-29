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

/-- The Berry phase accumulated along the closed rectangular loop
`(a,c) → (b,c) → (b,d) → (a,d) → (a,c)` in a two-dimensional parameter space,
for a Berry connection with components `A₁, A₂`.  It is the line integral
`∮ A₁ dx + A₂ dy` around the boundary of the rectangle `[a,b] × [c,d]`. -/

noncomputable def berryCurvatureFlux (F₁ F₂ : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  (∫ y in c..d, ∫ x in a..b, F₁ x y) - (∫ x in a..b, ∫ y in c..d, F₂ x y)

/-- Fundamental theorem of calculus in the first slot: integrating `∂₁A₂` in `x`
recovers the boundary values of `A₂`. -/
