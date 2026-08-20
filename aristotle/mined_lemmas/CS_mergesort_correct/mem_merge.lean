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

namespace CS

variable {α : Type*}

/-- Merge two lists with respect to a boolean comparison `le`. -/

theorem mem_merge {le : α → α → Bool} {xs ys : List α} {a : α} :
    a ∈ merge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm le xs ys).mem_iff, List.mem_append]

/-- Merging two sorted lists gives a sorted list. -/
