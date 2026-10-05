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


theorem subw_append_right (w v : ℕ) (h : w + v ≤ w + v) (y1 : Fin w → Bool)
    (y2 : Fin v → Bool) : subw w v (w + v) h (Fin.append y1 y2) = y2 := by
  funext j
  exact append_apply_right y1 y2 _ j (by simp [subw])

/-! ### Views: reading a block of the witness -/

/-- `view n w k f` is `f` applied to the assignment that keeps the input variables
`< n`, reads the witness block of length `w` starting at position `n + k`, and is
`false` elsewhere. -/
