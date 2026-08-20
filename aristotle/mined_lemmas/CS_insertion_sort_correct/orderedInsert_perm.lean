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

variable {α : Type*} [LinearOrder α]

/-- Insert `a` into the (assumed sorted) list `l`, keeping it sorted. -/

theorem orderedInsert_perm (a : α) (l : List α) : (orderedInsert a l).Perm (a :: l) := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [orderedInsert_cons]
      by_cases h : a ≤ b
      · simp [h]
      · simp only [h, if_false]
        exact ((ih.cons b).trans (List.Perm.swap a b l))

/-- Membership in `orderedInsert`. -/
