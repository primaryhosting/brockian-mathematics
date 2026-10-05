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


def daddEq (n : ℕ) (d1 d2 : GapData) : GapData where
  w := d1.w + 1
  pos := fun a => (!a (n + d1.w) && view n d1.w 0 d1.pos a) ||
                  (a (n + d1.w) && view n d1.w 0 d2.pos a)
  neg := fun a => (!a (n + d1.w) && view n d1.w 0 d1.neg a) ||
                  (a (n + d1.w) && view n d1.w 0 d2.neg a)

