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

lemma setLIntegral_comp_smul (mu : Measure E) [mu.IsAddHaarMeasure] (g : E → ℝ≥0∞)
    {lam : ℝ} (hlam : lam ≠ 0) {s : Set E} (hs : MeasurableSet s) :
    ∫⁻ x in s, g (lam • x) ∂mu
      = ENNReal.ofReal |(lam ^ (Module.finrank ℝ E))⁻¹| * ∫⁻ y in lam • s, g y ∂mu := by
  have hsmul : MeasurableSet (lam • s) := by
    rw [← Set.image_smul]
    exact ((Homeomorph.smulOfNeZero lam hlam).toMeasurableEquiv.measurableEmbedding).measurableSet_image'
      hs
  have hmapeq : Measure.map (fun x : E => lam • x) mu
      = ENNReal.ofReal |(lam ^ (Module.finrank ℝ E))⁻¹| • mu := Measure.map_addHaar_smul mu hlam
  have h1 : ∫⁻ y, (lam • s).indicator g y ∂(Measure.map (fun x : E => lam • x) mu)
      = ∫⁻ x, (lam • s).indicator g (lam • x) ∂mu :=
    lintegral_map_equiv _ (Homeomorph.smulOfNeZero lam hlam).toMeasurableEquiv
  have h2 : ∀ x : E, (lam • s).indicator g (lam • x) = s.indicator (fun x => g (lam • x)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((Set.smul_mem_smul_set_iff₀ hlam _ _).2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      intro hmem
      exact hx ((Set.smul_mem_smul_set_iff₀ hlam _ _).1 hmem)
  simp only [h2] at h1
  rw [hmapeq] at h1
  rw [lintegral_smul_measure, lintegral_indicator hsmul, lintegral_indicator hs] at h1
  exact h1.symm

/-- **Conformal invariance of the Yang–Mills energy in dimension four.**  Rescaling a Yang–Mills
field by a factor `lam > 0` transports its energy from a region `s` to the rescaled region,
without changing its value.  In particular the energy of the rescaled field on the ball of radius
`r/lam` equals the energy of the original field on the ball of radius `r`: energy can be
concentrated at arbitrarily small scales, which is exactly the mechanism of bubbling. -/
