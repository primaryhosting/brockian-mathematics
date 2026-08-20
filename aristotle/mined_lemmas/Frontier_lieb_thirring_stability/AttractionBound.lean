/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

def AttractionBound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b V : ℝ) (W ρ : α → ℝ) : Prop :=
  -(b * ∫ x, W x * ρ x ∂μ) ≤ V

/-- **Core stability estimate.** If the kinetic energy obeys a Lieb–Thirring bound and the
potential energy is bounded below by `-b ∫ W ρ`, then the total energy is bounded below by
`- ltConst Kc * b ^ (5/2) * ∫ W ^ (5/2)`, independently of the density `ρ`
(in particular, independently of the particle number). -/
