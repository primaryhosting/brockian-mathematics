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

/-- **Baire category theorem** for complete metric spaces: a countable family of dense
open sets in a complete (pseudo)metric space has dense intersection. -/
theorem baire_category {X : Type*} [PseudoEMetricSpace X] [CompleteSpace X]
    {ι : Sort*} [Countable ι] {f : ι → Set X}
    (ho : ∀ i, IsOpen (f i)) (hd : ∀ i, Dense (f i)) :
    Dense (⋂ i, f i) :=
  dense_iInter_of_isOpen ho hd

end Topology

namespace Topology

/-- Sequence version: the intersection of a sequence of dense open subsets of a complete
metric space is dense. -/
theorem baire_category_nat {X : Type*} [PseudoEMetricSpace X] [CompleteSpace X]
    {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) :=
  baire_category ho hd

/-- Version for a countable *set* of dense open sets. -/
theorem baire_category_sInter {X : Type*} [PseudoEMetricSpace X] [CompleteSpace X]
    {S : Set (Set X)} (hS : S.Countable) (ho : ∀ s ∈ S, IsOpen s) (hd : ∀ s ∈ S, Dense s) :
    Dense (⋂₀ S) :=
  dense_sInter_of_isOpen ho hS hd

/-- In a nonempty complete metric space, a countable intersection of dense open sets is
nonempty. -/
theorem baire_category_nonempty {X : Type*} [PseudoEMetricSpace X] [CompleteSpace X]
    [Nonempty X] {ι : Sort*} [Countable ι] {f : ι → Set X}
    (ho : ∀ i, IsOpen (f i)) (hd : ∀ i, Dense (f i)) :
    (⋂ i, f i).Nonempty :=
  (baire_category ho hd).nonempty

end Topology

#print axioms Topology.baire_category
#print axioms Topology.baire_category_nat
#print axioms Topology.baire_category_sInter
#print axioms Topology.baire_category_nonempty

