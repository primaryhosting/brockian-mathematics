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

open MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology

/-! ## The Yang–Mills energy

A Yang–Mills field on a manifold `X` is modelled here by its curvature `F : X → V`, a field with
values in a normed space `V` (in the geometric situation, `V` is the space of `𝔤`-valued
two-forms).  Its Yang–Mills energy over a region `s` is `∫_s ‖F‖²`. -/

section Energy

variable {X : Type*} [MeasurableSpace X] {V : Type*} [NormedAddCommGroup V]

/-- The Yang–Mills energy `∫_s ‖F‖²` of a curvature field `F` over the region `s`. -/

theorem removable_singularity_abelian {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R \ {c}))
    (hb : ∃ C : ℝ, ∀ z ∈ ball c R \ {c}, ‖f z‖ ≤ C) :
    DifferentiableOn ℂ (Function.update f c (limUnder (𝓝[≠] c) f)) (ball c R) := by
  obtain ⟨C, hC⟩ := hb
  refine Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds c hR) hd ?_
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hC z hz

end Frontier

section AxiomCheck
#print axioms Frontier.uhlenbeck_bubbling
#print axioms Frontier.energyOn_rescale
#print axioms Frontier.zero_mem_bubbleSet_rescale
#print axioms Frontier.removable_singularity_abelian
#print axioms Frontier.energyOn_diff_singleton
#print axioms Frontier.bubbleSet_eq_empty_of_energy_lt
end AxiomCheck

