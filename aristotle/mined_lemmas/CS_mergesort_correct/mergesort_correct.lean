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

theorem mergesort_correct (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b ∨ le b a) (l : List α) :
    List.Pairwise (fun a b => le a b = true) (msort le l) ∧ (msort le l).Perm l :=
  ⟨msort_pairwise le trans total l, msort_perm le l⟩

/-- Correctness of merge sort on a linear order, using `(· ≤ ·)` as the comparison. -/
