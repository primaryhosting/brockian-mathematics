import Mathlib

/-!
# Baire Category
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.baire_category
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

namespace Topology

/-- **Baire category theorem** for complete metric spaces: given a countable family
`f : ι → Set X` of dense open subsets of a complete metric space `X`, the intersection
`⋂ i, f i` is dense in `X`. -/

theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X]
    {ι : Sort*} [Countable ι] {f : ι → Set X}
    (ho : ∀ i, IsOpen (f i)) (hd : ∀ i, Dense (f i)) :
    Dense (⋂ i, f i) :=
  dense_iInter_of_isOpen ho hd

/-- Set-indexed form of the Baire category theorem: a countable collection `S` of dense
open subsets of a complete metric space has dense intersection `⋂₀ S`. -/
