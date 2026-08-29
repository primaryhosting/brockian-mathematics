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

/-
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem wt_mul_aux (p1 n1 p2 n2 : Bool) (h1 : p1 = true → n1 = true → False)
    (h2 : p2 = true → n2 = true → False) :
    (if (p1 && p2) || (n1 && n2) then (1 : ℤ) else if (p1 && n2) || (n1 && p2) then -1 else 0)
      = (if p1 then (1 : ℤ) else if n1 then -1 else 0) *
        (if p2 then (1 : ℤ) else if n2 then -1 else 0) := by
  revert h1 h2
  cases p1 <;> cases n1 <;> cases p2 <;> cases n2 <;> simp

