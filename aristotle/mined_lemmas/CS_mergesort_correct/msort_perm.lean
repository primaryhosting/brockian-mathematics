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

theorem msort_perm (le : α → α → Bool) (l : List α) : (msort le l).Perm l := by
  induction l using CS.msort.induct with
  | case1 => simp [msort]
  | case2 x => simp [msort]
  | case3 x y t ih1 ih2 =>
      rw [msort]
      refine (merge_perm le _ _).trans ?_
      exact (ih1.append ih2).trans (by rw [List.take_append_drop])

/-- `msort` returns a sorted list, for any transitive and total comparison. -/
