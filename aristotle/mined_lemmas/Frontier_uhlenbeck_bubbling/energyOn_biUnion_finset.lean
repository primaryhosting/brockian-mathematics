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

lemma energyOn_biUnion_finset {mu : Measure X} {F : X → V} {ι : Type*} {S : Finset ι}
    {t : ι → Set X} (hd : Set.PairwiseDisjoint (↑S) t) (hm : ∀ b ∈ S, MeasurableSet (t b)) :
    energyOn mu F (⋃ b ∈ S, t b) = ∑ b ∈ S, energyOn mu F (t b) :=
  lintegral_biUnion_finset hd hm _

end Energy

/-! ## Bubbling: the concentration set of a sequence of Yang–Mills fields -/

section Bubble

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {V : Type*} [NormedAddCommGroup V]

/-- The *bubbling set* (concentration set) at threshold `eps` of a sequence `F` of curvature
fields: the points `x` such that, on *every* ball around `x`, the energy of `F n` is eventually
at least `eps`.  These are exactly the points where energy can concentrate ("bubble off") in the
limit. -/
