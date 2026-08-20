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

set_option grind.warning false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Merge two lists, assumed sorted, into one list. -/

theorem merge_cons_cons (a b : α) (as bs : List α) :
    merge (a :: as) (b :: bs) =
      if a ≤ b then a :: merge as (b :: bs) else b :: merge (a :: as) bs := by
  simp [merge]

