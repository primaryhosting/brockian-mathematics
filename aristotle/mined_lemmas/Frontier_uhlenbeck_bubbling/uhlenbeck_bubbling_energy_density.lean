/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
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

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

/-- The *bubbling set* (concentration set) of a sequence of energy measures `mu n` at
concentration threshold `eps`: those points where, at every scale `r > 0`, at least `eps`
of the energy is asymptotically present. -/

theorem uhlenbeck_bubbling_energy_density {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {V : Type*} [NormedAddCommGroup V]
    (vol : Measure X) (F : ℕ → X → V) (E eps : ℝ≥0∞) (hE : E ≠ ⊤) (heps : eps ≠ 0)
    (hbound : ∀ n, ∫⁻ x, ‖F n x‖ₑ ^ 2 ∂vol ≤ E) :
    (BubbleSet (fun n => vol.withDensity (fun x => ‖F n x‖ₑ ^ 2)) eps).Finite ∧
      ((BubbleSet (fun n => vol.withDensity (fun x => ‖F n x‖ₑ ^ 2)) eps).ncard : ℝ≥0∞) * eps
        ≤ E := by
  refine uhlenbeck_bubbling _ E eps hE heps (fun n => ?_)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hbound n

end Frontier

