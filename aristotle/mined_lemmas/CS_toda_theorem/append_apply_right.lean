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


theorem append_apply_right {w v : ℕ} (y1 : Fin w → Bool) (y2 : Fin v → Bool)
    (i : Fin (w + v)) (j : Fin v) (hij : (i : ℕ) = w + (j : ℕ)) :
    Fin.append y1 y2 i = y2 j := by
  have : i = Fin.natAdd w j := Fin.ext (by simpa using hij)
  rw [this, Fin.append_right]

