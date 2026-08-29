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

/-- **Baire category theorem** (complete metric space version): in a complete metric space,
the intersection of a countable family of dense open sets is dense. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X]
    {ι : Type*} [Countable ι] {S : ι → Set X}
    (hopen : ∀ i, IsOpen (S i)) (hdense : ∀ i, Dense (S i)) :
    Dense (⋂ i, S i) :=
  dense_iInter_of_isOpen hopen hdense

/-- Sequence form of the Baire category theorem. -/
theorem baire_category_nat {X : Type*} [MetricSpace X] [CompleteSpace X] {S : ℕ → Set X}
    (hopen : ∀ n, IsOpen (S n)) (hdense : ∀ n, Dense (S n)) :
    Dense (⋂ n, S n) :=
  baire_category hopen hdense

/-- Set-indexed form: the intersection of a countable collection of dense open subsets of a
complete metric space is dense. -/
theorem baire_category_sInter {X : Type*} [MetricSpace X] [CompleteSpace X] {C : Set (Set X)}
    (hcount : C.Countable) (hopen : ∀ s ∈ C, IsOpen s) (hdense : ∀ s ∈ C, Dense s) :
    Dense (⋂₀ C) :=
  dense_sInter_of_isOpen hopen hcount hdense

/-- In a nonempty complete metric space, a countable intersection of dense open sets is
nonempty. -/
theorem baire_category_nonempty {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] {S : ι → Set X}
    (hopen : ∀ i, IsOpen (S i)) (hdense : ∀ i, Dense (S i)) :
    (⋂ i, S i).Nonempty :=
  (baire_category hopen hdense).nonempty

end Topology

#print axioms Topology.baire_category
#print axioms Topology.baire_category_nat
#print axioms Topology.baire_category_sInter
#print axioms Topology.baire_category_nonempty

