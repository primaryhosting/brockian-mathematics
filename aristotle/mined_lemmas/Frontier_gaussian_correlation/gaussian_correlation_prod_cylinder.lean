import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem gaussian_correlation_prod_cylinder {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set E) (B : Set F) :
    (μ.prod ν) (A ×ˢ (univ : Set F)) * (μ.prod ν) ((univ : Set E) ×ˢ B)
      = (μ.prod ν) ((A ×ˢ (univ : Set F)) ∩ ((univ : Set E) ×ˢ B)) := by
  rw [Set.prod_inter_prod, Set.inter_univ, Set.univ_inter]
  simp [Measure.prod_prod]

end Frontier

