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

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: this Lean toolchain requires `import` to be the very first command in a file, so the
required header comment appears immediately after the import.)
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Real BigOperators

namespace Brockian.Equidistribution

/-- The circle `ℝ / ℤ`, on which we study equidistribution. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

noncomputable instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨by simp⟩

/-- Continuous functions on the (compact) circle are integrable for any finite measure. -/

lemma norm_integral_sub_le (μ : Measure Circ) [IsProbabilityMeasure μ] (f g : C(Circ, ℂ)) :
    ‖(∫ t, f t ∂μ) - ∫ t, g t ∂μ‖ ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_continuousMap f μ) (integrable_continuousMap g μ)]
  have h : ∀ t : Circ, ‖f t - g t‖ ≤ ‖f - g‖ := by
    intro t
    have := ContinuousMap.norm_coe_le_norm (f - g) t
    simpa using this
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖f - g‖)
    (f := fun t => f t - g t) (Filter.Eventually.of_forall h)
  simpa using this

/-! ### The empirical measures -/

/-- The empirical measure of the first `N + 1` terms of a sequence in the circle. -/
