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

noncomputable def berryPhaseLoop (A₁ A₂ : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  (∫ x in a..b, A₁ x c) + (∫ y in c..d, A₂ b y)
    - (∫ x in a..b, A₁ x d) - (∫ y in c..d, A₂ a y)

/-- The flux of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` through the rectangle
`[a,b] × [c,d]`, written as a difference of iterated integrals of the two
partial derivatives `F₁ = ∂₁A₂` and `F₂ = ∂₂A₁`. -/
