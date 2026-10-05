/-
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/--
**Baire category theorem.**
A (nonempty) complete metric space is not a countable union of nowhere dense sets.

Here `IsNowhereDense s` means `interior (closure s) = ∅`.

The proof uses the Mathlib instance making a complete (pseudo)metric space a `BaireSpace`,
together with `isMeagre_iUnion` (a countable union of meagre sets is meagre),
`IsNowhereDense.isMeagre`, and `not_isMeagre_of_isOpen` (in a Baire space a nonempty open
set is not meagre).
-/

theorem exists_notMem_iUnion_of_isNowhereDense {X : Type*} [MetricSpace X] [CompleteSpace X]
    [Nonempty X] {ι : Type*} [Countable ι] (s : ι → Set X) (hs : ∀ i, IsNowhereDense (s i)) :
    ∃ x : X, ∀ i, x ∉ s i := by
  by_contra hc
  push_neg at hc
  refine baire_category s hs (Set.eq_univ_of_forall fun x => ?_)
  obtain ⟨i, hi⟩ := hc x
  exact Set.mem_iUnion.2 ⟨i, hi⟩

end Math

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

