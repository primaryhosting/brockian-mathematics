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

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma isAntichain_rk_level (i : ℕ) :
    IsAntichain (· ≤ ·) ((Finset.univ.filter (fun z : α => rk z = i) : Finset α) : Set α) := by
  intro a ha b hb hab hle
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
  have : a < b := lt_of_le_of_ne hle hab
  have := rk_lt_rk this
  omega

/-- The cover of the order by the level sets of the rank function. -/
