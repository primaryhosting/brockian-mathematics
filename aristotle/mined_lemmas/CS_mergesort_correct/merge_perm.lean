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

theorem merge_perm (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).Perm (xs ++ ys) := by
  induction xs, ys using CS.merge.induct (le := le) with
  | case1 ys => simp [merge]
  | case2 xs h => simp [merge]
  | case3 x xs y ys h ih =>
      rw [merge]; simp only [h, if_true]
      exact (ih.cons x).trans (by simp)
  | case4 x xs y ys h ih =>
      rw [merge]; simp only [h, if_false, Bool.false_eq_true]
      exact (ih.cons y).trans List.perm_middle.symm

