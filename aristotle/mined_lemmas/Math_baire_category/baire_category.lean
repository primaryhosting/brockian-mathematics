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

namespace Math

/-- **Baire category theorem**: a nonempty complete (pseudo)metric space is not the union of
a countable family of nowhere dense sets. -/

theorem baire_category {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] (f : ι → Set X) (hf : ∀ i, IsNowhereDense (f i)) :
    (Set.univ : Set X) ≠ ⋃ i, f i := by
  intro h
  have hmeagre : IsMeagre (Set.univ : Set X) :=
    h ▸ isMeagre_iUnion fun i => (hf i).isMeagre
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hmeagre

end Math

