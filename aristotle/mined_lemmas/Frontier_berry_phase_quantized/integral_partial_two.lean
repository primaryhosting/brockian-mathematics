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

theorem integral_partial_two (A₁ F₂ : ℝ → ℝ → ℝ)
    (hderiv : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A₁ x t) (F₂ x y) y)
    (hcont : Continuous fun p : ℝ × ℝ => F₂ p.1 p.2) (c d x : ℝ) :
    (∫ y in c..d, F₂ x y) = A₁ x d - A₁ x c := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv x y) ?_
  exact (hcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d

/-- **Berry phase = flux of the Berry curvature, and quantization.**

For a smooth Berry connection `A = (A₁, A₂)` on a two-dimensional parameter
space, with Berry curvature `F = ∂₁A₂ - ∂₂A₁`:

* the Berry phase around the closed rectangular loop bounding `[a,b] × [c,d]`
  equals the flux of the Berry curvature through that rectangle (Stokes/Green);
* consequently, whenever that flux is an integer multiple of `2π` (a quantized
  Chern-type flux), the Berry phase factor `exp (i γ)` equals `1`. -/
