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

theorem energyOn_diff_singleton {V : Type*} [NormedAddCommGroup V] (F : E4 → V) (s : Set E4)
    (c : E4) : energyOn volume F (s \ {c}) = energyOn volume F s := by
  have hnull : (volume : Measure E4) {c} = 0 := measure_singleton c
  have hae : (s \ {c} : Set E4) =ᵐ[(volume : Measure E4)] s := diff_null_ae_eq_self hnull
  unfold energyOn
  exact setLIntegral_congr hae

/-- **Removable singularity, abelian base case.**  For an abelian (`U(1)`) Yang–Mills field on a
disc, the field equation says that the connection form is (anti)holomorphic; Riemann's removable
singularity theorem then shows that a field which is holomorphic on the punctured disc and
bounded near the puncture extends holomorphically across it.  This is the base case of the
Uhlenbeck removable singularity theorem. -/
