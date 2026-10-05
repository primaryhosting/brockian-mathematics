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
open scoped Classical

open Set MeasureTheory

namespace Frontier

/-- The **Berry connection** is modelled as a real one-form on a two-dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose value `A p = (A₁ p, A₂ p)` gives the components
of the form `A₁ dx + A₂ dy` at the parameter point `p`. -/
abbrev BerryConnection := ℝ × ℝ → ℝ × ℝ

/-- The **Berry curvature** of a Berry connection `A` at a parameter point `p`:
`F = ∂₁ A₂ - ∂₂ A₁`, the exterior derivative of the connection one-form. -/

noncomputable def berryFlux (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y)

/-- **Berry phase = integral of the Berry curvature.**  For a differentiable Berry connection
whose curvature is integrable on the rectangle, the Berry phase around the (counterclockwise)
boundary loop of the rectangle equals the flux of the Berry curvature through it. -/
