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
open scoped Interval

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory intervalIntegral Set

/-- The Berry connection is modelled as a (real) one-form on a two–dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose components `(A p).1`, `(A p).2` are the
components `A₁`, `A₂` of the connection at the parameter point `p`. -/

noncomputable def berryPhase (A : ℝ × ℝ → ℝ × ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, (A (x, a₂)).1) + ∫ y in a₂..b₂, (A (b₁, y)).2) -
    ((∫ x in a₁..b₁, (A (x, b₂)).1) + ∫ y in a₂..b₂, (A (a₁, y)).2)

/-- **Berry phase from the Berry curvature.**
For a continuously differentiable Berry connection `A` on a two–dimensional parameter
space, the Berry phase around the closed rectangular loop bounding
`[a₁, b₁] × [a₂, b₂]` equals the integral of the Berry curvature
`F = ∂₁A₂ - ∂₂A₁` over the enclosed region. -/
