/-!
# Baire Category
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Topology

/-- **Baire category theorem** for complete (pseudo)metric spaces: in a complete metric
space `X`, the intersection of a countable family of dense open subsets is dense. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X]
    {ι : Type*} [Countable ι] (f : ι → Set X)
    (ho : ∀ i, IsOpen (f i)) (hd : ∀ i, Dense (f i)) :
    Dense (⋂ i, f i) :=
  dense_iInter_of_isOpen ho hd

/-- Version for a countable indexed family of sets given by a countable set of indices. -/
theorem baire_category_sInter {X : Type*} [MetricSpace X] [CompleteSpace X]
    {S : Set (Set X)} (hS : S.Countable)
    (ho : ∀ s ∈ S, IsOpen s) (hd : ∀ s ∈ S, Dense s) :
    Dense (⋂₀ S) :=
  hS.dense_sInter_of_isOpen ho hd

end Topology

